use ark_poly::{univariate::DensePolynomial as UnivariatePolynomial, DenseUVPolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain 
    // Polynomial
};
use std::marker::PhantomData;
use ark_ec::pairing::Pairing;
use my_kzg::{
    biv_batch_kzg::BivBatchKZG, biv_trivial_kzg::{BivariateKZG, BivariatePolynomial}, par_join_3, uni_batch_kzg::BatchKZG 
};
use ark_ff::{Zero, Field, One};
use rayon::prelude::*;
use crate::prover_pre::{DeValPolys, NPolys, DeLowerAandBEvals, DeLowerAandBPolys};
use my_ipa::de_ipa::DeIPA;
use ark_std::error::Error;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use itertools::MultiUnzip;
use de_network::{DeMultiNet as Net, DeNet};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
// use serde::{Serialize, Deserialize};
use crate::impl_serde_for_ark_serde_unchecked;

// Given public matrices Pa, Pb, Pc \in F^{ml} \times F^{ml}, split each of them into l sub-matrices
// Each sub-matrix in \in F^{ml} \times F^{m}
// Assume the sub-matrices have at most m' (m_prime) non-zero-entries, and m' should be power-of-two, padding if not
// Say M with order m' and generator g
// Assume the non-zero entries are presented in some canonical order (e.g., row-wise or column-wise) and works for all row, col, and val

// The original data of row non-zero entry index vectors for some **sub-prover**, ie, some **sub-matrix**
// The row index belongs to [0, ml-1]; we introduce row_low, row_high belonging to [0, sqrt{ml}-1] to describe it
// row(g^i) = the row index of the (i-1)-th non-zero entry = row_low(g^i) + sqrt{ml} * row_high(g^i)
// The value choice of row_low and row_high are unique

// if some sub-matrix has m'' < m' non-zero entries, define arbitrary values for these (m' - m'') entries, here use 0

// The values should be field_elements, but we requre usize to do the pow operation
// Luckily, [0, ml-1] is smaller enough on a field, so just transform it to usize directly
#[derive(Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct DeRowIndex {
    pub row_pa_low: Vec<usize>,
    pub row_pa_high: Vec<usize>,
    pub row_pb_low: Vec<usize>,
    pub row_pb_high: Vec<usize>,
    pub row_pc_low: Vec<usize>,
    pub row_pc_high: Vec<usize>,
}

impl DeRowIndex {
    pub fn new() -> Self {
        Self {
            row_pa_low: vec![],
            row_pa_high: vec![],
            row_pb_low: vec![],
            row_pb_high: vec![],
            row_pc_low: vec![],
            row_pc_high: vec![],
        }
    }

    pub fn padding(
        &mut self,
        n: usize,
    ) {
        let len_a_low = self.row_pa_low.len();
        let len_a_high = self.row_pa_high.len();
        let len_b_low = self.row_pb_low.len();
        let len_b_high = self.row_pb_high.len();
        let len_c_low = self.row_pc_low.len();
        let len_c_high = self.row_pc_high.len();
        self.row_pa_low.append(&mut vec![0usize; n - len_a_low]);
        self.row_pa_high.append(&mut vec![0usize; n - len_a_high]);
        self.row_pb_low.append(&mut vec![0usize; n - len_b_low]);
        self.row_pb_high.append(&mut vec![0usize; n - len_b_high]);        
        self.row_pc_low.append(&mut vec![0usize; n - len_c_low]);
        self.row_pc_high.append(&mut vec![0usize; n - len_c_high]);
    }
}

// The original data of col non-zero entry index vectors for some **sub-prover**, ie, some **sub-matrix**
// Note col has the same non-zero entry order with row
// if some sub-matrix has m'' < m' non-zero entries, define arbitrary values for these (m' - m'') entries, here use 0
#[derive(Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct DeColIndex {
    pub col_pa: Vec<usize>,
    pub col_pb: Vec<usize>,
    pub col_pc: Vec<usize>,
}

impl DeColIndex {
    pub fn new() -> Self {
        Self {
            col_pa: vec![],
            col_pb: vec![],
            col_pc: vec![],
        }
    }

    pub fn padding(
        &mut self,
        n: usize,
    ) {
        let len_a = self.col_pa.len();
        let len_b = self.col_pb.len();
        let len_c = self.col_pc.len();
        self.col_pa.append(&mut vec![0usize; n - len_a]);
        self.col_pb.append(&mut vec![0usize; n - len_b]);
        self.col_pc.append(&mut vec![0usize; n - len_c]);
    }
}
// The original data of val non-zero entry index vectors for some **sub-prover**, ie, some **sub-matrix**
// Note val has the same non-zero entry order with row
// Here we use Field elements
// if some sub-matrix has m'' < m' non-zero entries, define arbitrary values for these (m' - m'') entries, here use 0
#[derive(Clone, Debug)]
pub struct DeValEvals<P: Pairing> {
    pub evals_val_pa: Vec<P::ScalarField>,
    pub evals_val_pb: Vec<P::ScalarField>,
    pub evals_val_pc: Vec<P::ScalarField>,
}

impl<P: Pairing> DeValEvals<P> {
    pub fn new() -> Self {
        Self {
            evals_val_pa: vec![],
            evals_val_pb: vec![],
            evals_val_pc: vec![],
        }
    }

    pub fn padding(
        &mut self,
        n: usize,
    ) {
        let f_zero = P::ScalarField::zero();
        let len_a = self.evals_val_pa.len();
        let len_b = self.evals_val_pb.len();
        let len_c = self.evals_val_pc.len();
        self.evals_val_pa.append(&mut vec![f_zero; n - len_a]);
        self.evals_val_pb.append(&mut vec![f_zero; n - len_b]);
        self.evals_val_pc.append(&mut vec![f_zero; n - len_c]);
    }
}

// The lookup frequency parameters
// Each polys are defined over subgroup H with size m, say generator w
// For col, n_col(w^i) = the times of {col(x)} equals to i, for i \in [0, m-1]
// For row, n_row_low(w^i) / n_row_high(w^i) = the times of {row_low(x)} / {row_high(x)} equals to i
// For row, when m > i > sqrt{ml}, n_row_low(w^i) / n_row_high(w^i) = 0
// Note that {col(x)}, {row_low(x)} / {row_high(x)} can equal to 0
#[derive(Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct NEvals<P: Pairing> {
    pub row_pa_low: Vec<P::ScalarField>,
    pub row_pa_high: Vec<P::ScalarField>,
    pub row_pb_low: Vec<P::ScalarField>,
    pub row_pb_high: Vec<P::ScalarField>,
    pub row_pc_low: Vec<P::ScalarField>,
    pub row_pc_high: Vec<P::ScalarField>,
    pub col_pa: Vec<P::ScalarField>,
    pub col_pb: Vec<P::ScalarField>,
    pub col_pc: Vec<P::ScalarField>,
}


#[derive(Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct PreMesProver<P: Pairing> {
    pub upper_r_polys: Vec<UnivariatePolynomial<P::ScalarField>>,
    pub de_row_index_vecs: Vec<DeRowIndex>,
    pub de_col_index_vecs: Vec<DeColIndex>,
    pub val_polys: Vec<DeValPolys<P>>,
    pub total_lower_a_b_evals: Vec<DeLowerAandBEvals<P>>,
    pub total_lower_a_b_polys: Vec<DeLowerAandBPolys<P>>,
    pub n_evals: NEvals<P>,
    pub n_polys: NPolys<P>
}

#[derive(Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct PreMesVerifier<P: Pairing> {
    pub com_upper_r: P::G1,
    pub coms_val: Vec<P::G1>,
    pub coms_lower_a_b: Vec<P::G1>,
    pub com_l: P::G1,
    pub coms_n: Vec<P::G1>
}

impl_serde_for_ark_serde_unchecked!(PreMesProver);
impl_serde_for_ark_serde_unchecked!(PreMesVerifier);

pub struct Indexer<P: Pairing> {
    _pairing: PhantomData<P>,
}

impl<P: Pairing> Indexer<P> {

    pub fn preprocess (
        m: usize,
        l: usize,
        cs: &ConstraintSystemRef<P::ScalarField>,
        powers: &Vec<Vec<P::G1Affine>>,
        m_powers: &Vec<Vec<P::G1Affine>>,
        x_srs: &Vec<P::G1Affine>,
        x_domain: &GeneralEvaluationDomain<P::ScalarField>,
        y_domain: &GeneralEvaluationDomain<P::ScalarField>,
        m_domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> (PreMesProver<P>, PreMesVerifier<P>) {
        let (de_row_index_vecs, de_col_index_vecs, de_val_evals_vecs, m_prime): (Vec<_>, Vec<_>, Vec<_>, usize) = Indexer::<P>::build_de_r1cs_index(l, m, &cs).unwrap();
        let (upper_r_polys, com_upper_r) = Indexer::<P>::compute_and_commit_poly_upper_r(&powers, l);
        let val_polys = Indexer::<P>::compute_val_polys(l, &m_domain, &de_val_evals_vecs);
        let coms_val = Indexer::<P>::commit_val_polys(&m_powers, &val_polys);
        let total_lower_a_b_evals_and_polys: Vec<(DeLowerAandBEvals<P>, DeLowerAandBPolys<P>)> = {
            (0..Net::n_parties()).into_par_iter().map(|i| Indexer::<P>::compute_lower_a_b_evals_and_polys(i, &de_row_index_vecs, &de_col_index_vecs, &m_domain, &x_domain)).collect()
        };
        let (total_lower_a_b_evals, total_lower_a_b_polys): (Vec<DeLowerAandBEvals<P>>, Vec<DeLowerAandBPolys<P>>) = {
            (
                total_lower_a_b_evals_and_polys.par_iter().map(|eval_poly| eval_poly.0.clone()).collect(), 
                total_lower_a_b_evals_and_polys.par_iter().map(|eval_poly| eval_poly.1.clone()).collect(), 
            )
        };
        let coms_lower_a_b = Indexer::<P>::commit_lower_a_b_polys(&m_powers, &total_lower_a_b_polys);
        let n_evals = Indexer::<P>::build_n_evals(&de_row_index_vecs, &de_col_index_vecs, l, m, m_prime);
        let n_polys = Indexer::<P>::compute_n_polys(&x_domain, &n_evals);
        let coms_n = Indexer::<P>::commit_n_polys(&x_srs, &n_polys);
        let com_l = Indexer::<P>::commit_poly_upper_l(&powers, l, &y_domain);

        (
            PreMesProver{upper_r_polys, de_row_index_vecs, de_col_index_vecs, val_polys, total_lower_a_b_evals, total_lower_a_b_polys, n_evals, n_polys}, 
            PreMesVerifier{com_upper_r, coms_val, coms_lower_a_b, com_l, coms_n}
        )
    }

    // Create a new `Preprocessing` from the cs and domains and write it to a file.
    pub fn new_to_file(
        m: usize,
        l: usize,
        cs: &ConstraintSystemRef<P::ScalarField>,
        powers: &Vec<Vec<P::G1Affine>>,
        m_powers: &Vec<Vec<P::G1Affine>>,
        x_srs: &Vec<P::G1Affine>,
        x_domain: &GeneralEvaluationDomain<P::ScalarField>,
        y_domain: &GeneralEvaluationDomain<P::ScalarField>,
        m_domain: &GeneralEvaluationDomain<P::ScalarField>,
        file_path: &str
    ) -> Result<(), Box<dyn Error>> {
        let (pre_mes_prover, pre_mes_verifier) = Self::preprocess(m, l, cs, powers, m_powers, x_srs, x_domain, y_domain, m_domain);
        let file = std::fs::File::create(file_path)?;
        let writer = std::io::BufWriter::new(file);
        bincode::serialize_into(writer, &(pre_mes_prover, pre_mes_verifier))?;
        Ok(())
    }

    pub fn read_from_file(
        file_path: &str,
    ) -> Result<(PreMesProver<P>, PreMesVerifier<P>), Box<dyn Error>> {
        let file = std::fs::File::open(file_path)?;
        let reader = std::io::BufReader::new(file);
        let (pre_mes_prover, pre_mes_verifier) = bincode::deserialize_from(reader)?;
        Ok((pre_mes_prover, pre_mes_verifier))
    }

    fn decompose(
        v: usize,
        sqrt_ml: usize,
    ) -> (usize, usize) {
        let high = v / sqrt_ml as usize;
        let low = v - high * sqrt_ml;
        (low, high)
    }

    pub fn build_de_r1cs_index(
        l: usize,
        m: usize,
        cs: &ConstraintSystemRef<P::ScalarField>,
    )-> Result<(Vec<DeRowIndex>, Vec<DeColIndex>, Vec<DeValEvals<P>>, usize), SynthesisError> {
        let cs = cs.borrow().unwrap();
        let cs_matrix = cs.to_matrices().unwrap();
        let ml = m * l;
        let sqrt_ml = (ml as f64).sqrt() as usize;
        assert_eq!(cs_matrix.a.len(), ml);

        let (mut de_row_index_vecs, mut de_col_index_vecs, mut de_val_evals_vecs): (Vec<_>, Vec<_>, Vec<_>) = 
            (0..l).map(|_| {(
                DeRowIndex::new(),
                DeColIndex::new(),
                DeValEvals::<P>::new(),
            )}).multiunzip();

        let mut m_prime_a_vecs = vec![0usize; l];
        let mut m_prime_b_vecs = vec![0usize; l];
        let mut m_prime_c_vecs = vec![0usize; l];

        for row_id in 0..ml {
            cs_matrix.a[row_id].iter().for_each(|(val, col_id)| {
                // current entry: ((row_id, col_id), val)
                let sub_prover_id = col_id / m;
                        
                let (low, high) = Self::decompose(row_id, sqrt_ml);
                de_row_index_vecs[sub_prover_id].row_pa_low.push(low);
                de_row_index_vecs[sub_prover_id].row_pa_high.push(high);

                de_col_index_vecs[sub_prover_id].col_pa.push(*col_id % m);

                de_val_evals_vecs[sub_prover_id].evals_val_pa.push(P::ScalarField::from(*val));

                m_prime_a_vecs[sub_prover_id] += 1;
            });
                
            cs_matrix.b[row_id].iter().for_each(|(val, col_id)| {
                let sub_prover_id = col_id / m;
                        
                let (low, high) = Self::decompose(row_id, sqrt_ml);
                de_row_index_vecs[sub_prover_id].row_pb_low.push(low);
                de_row_index_vecs[sub_prover_id].row_pb_high.push(high);

                de_col_index_vecs[sub_prover_id].col_pb.push(*col_id % m);

                de_val_evals_vecs[sub_prover_id].evals_val_pb.push(P::ScalarField::from(*val));

                m_prime_b_vecs[sub_prover_id] += 1;
            });
                    
            cs_matrix.c[row_id].iter().for_each(|(val, col_id)| {
                let sub_prover_id = col_id / m;
                        
                let (low, high) = Self::decompose(row_id, sqrt_ml);
                de_row_index_vecs[sub_prover_id].row_pc_low.push(low);
                de_row_index_vecs[sub_prover_id].row_pc_high.push(high);

                de_col_index_vecs[sub_prover_id].col_pc.push(*col_id % m);

                de_val_evals_vecs[sub_prover_id].evals_val_pc.push(P::ScalarField::from(*val));

                m_prime_c_vecs[sub_prover_id] += 1;
            });
        }

        // Padding
        let m_prime: usize = m_prime_a_vecs
            .into_iter()
            .chain(m_prime_b_vecs.into_iter())
            .chain(m_prime_c_vecs.into_iter())
            .max().unwrap();
        let pow_of_two = m_prime.next_power_of_two();

        for sub_prover_id in 0..l {
            de_row_index_vecs[sub_prover_id].padding(pow_of_two);
            de_col_index_vecs[sub_prover_id].padding(pow_of_two);
            de_val_evals_vecs[sub_prover_id].padding(pow_of_two);
        }

        Ok((de_row_index_vecs, de_col_index_vecs, de_val_evals_vecs, pow_of_two))
    }

    pub fn build_n_evals(
        de_row_index_vecs: &Vec<DeRowIndex>, 
        de_col_index_vecs: &Vec<DeColIndex>,
        l: usize,
        m: usize,
        len: usize,
    )-> NEvals<P> {
        let mut row_pa_low = vec![0u64; m];
        let mut row_pa_high = vec![0u64; m];
        let mut row_pb_low = vec![0u64; m];
        let mut row_pb_high = vec![0u64; m];
        let mut row_pc_low = vec![0u64; m];
        let mut row_pc_high = vec![0u64; m];
        let mut col_pa = vec![0u64; m];
        let mut col_pb = vec![0u64; m];
        let mut col_pc = vec![0u64; m];

        for sub_prover_id in 0..l {
            for i in 0..len {
                row_pa_low[de_row_index_vecs[sub_prover_id].row_pa_low[i]] += 1;
                row_pa_high[de_row_index_vecs[sub_prover_id].row_pa_high[i]] += 1;
                row_pb_low[de_row_index_vecs[sub_prover_id].row_pb_low[i]] += 1;
                row_pb_high[de_row_index_vecs[sub_prover_id].row_pb_high[i]] += 1;
                row_pc_low[de_row_index_vecs[sub_prover_id].row_pc_low[i]] += 1;
                row_pc_high[de_row_index_vecs[sub_prover_id].row_pc_high[i]] += 1;

                col_pa[de_col_index_vecs[sub_prover_id].col_pa[i]] += 1;
                col_pb[de_col_index_vecs[sub_prover_id].col_pb[i]] += 1;
                col_pc[de_col_index_vecs[sub_prover_id].col_pc[i]] += 1;
            }
        }

        let (row_pa_low, row_pa_high, row_pb_low, row_pb_high, 
            row_pc_low, row_pc_high, col_pa, col_pb, col_pc) = 
                (0..m).map(|i| {(
                    P::ScalarField::from(row_pa_low[i]),
                    P::ScalarField::from(row_pa_high[i]),
                    P::ScalarField::from(row_pb_low[i]),
                    P::ScalarField::from(row_pb_high[i]),
                    P::ScalarField::from(row_pc_low[i]),
                    P::ScalarField::from(row_pc_high[i]),
                    P::ScalarField::from(col_pa[i]),
                    P::ScalarField::from(col_pb[i]),
                    P::ScalarField::from(col_pc[i]),
                )}).multiunzip();

        NEvals {
            row_pa_low,
            row_pa_high,
            row_pb_low,
            row_pb_high,
            row_pc_low,
            row_pc_high,
            col_pa,
            col_pb,
            col_pc,
        }
    }

    pub fn compute_val_polys (
        l: usize,
        m_domain: &GeneralEvaluationDomain<P::ScalarField>,
        val_evals: &Vec<DeValEvals<P>>,
    ) -> Vec<DeValPolys<P>> {
        (0..l).into_par_iter().map(|i| {
            let (val_pa, val_pb, val_pc) = par_join_3!(
                || {
                    let eval_domain_val_pa = Evaluations::<P::ScalarField>::from_vec_and_domain(val_evals[i].evals_val_pa.clone(), *m_domain);
                    eval_domain_val_pa.interpolate()
                },
                || {
                    let eval_domain_val_pb = Evaluations::<P::ScalarField>::from_vec_and_domain(val_evals[i].evals_val_pb.clone(), *m_domain);
                    eval_domain_val_pb.interpolate()
                }, 
                || {
                    let eval_domain_val_pc = Evaluations::<P::ScalarField>::from_vec_and_domain(val_evals[i].evals_val_pc.clone(), *m_domain);
                    eval_domain_val_pc.interpolate()
                }
            );
            DeValPolys { val_pa, val_pb, val_pc}
        }).collect()
    }

    pub fn commit_val_polys (
        m_powers: &Vec<Vec<P::G1Affine>>,
        val_total_polys: &Vec<DeValPolys<P>>,
    ) -> Vec<P::G1> {
        let x_polys_val_a: Vec<UnivariatePolynomial<P::ScalarField>> = val_total_polys.par_iter().map(|polys| polys.val_pa.clone()).collect();
        let x_polys_val_b: Vec<UnivariatePolynomial<P::ScalarField>> = val_total_polys.par_iter().map(|polys| polys.val_pb.clone()).collect();
        let x_polys_val_c: Vec<UnivariatePolynomial<P::ScalarField>> = val_total_polys.par_iter().map(|polys| polys.val_pc.clone()).collect();

        let biv_poly_val_a = BivariatePolynomial{x_polynomials: x_polys_val_a};
        let biv_poly_val_b = BivariatePolynomial{x_polynomials: x_polys_val_b};
        let biv_poly_val_c = BivariatePolynomial{x_polynomials: x_polys_val_c};

        let bivariate_polynomials = vec![biv_poly_val_a, biv_poly_val_b, biv_poly_val_c];
        let coms_val = BivBatchKZG::<P>::commit(&m_powers, &bivariate_polynomials).unwrap();

        coms_val
    }

    pub fn compute_n_polys (
        x_domain: &GeneralEvaluationDomain<P::ScalarField>,
        n_evals: &NEvals<P>,
    ) -> NPolys<P> {

        let ((row_pa_low, row_pa_high, row_pb_low), (row_pb_high, row_pc_low, row_pc_high), (col_pa, col_pb, col_pc)) = par_join_3!(
            || {
                let row_pa_low = DeIPA::<P>::interpolate_from_eval_domain(&n_evals.row_pa_low, &x_domain);
                let row_pa_high = DeIPA::<P>::interpolate_from_eval_domain(&n_evals.row_pa_high, &x_domain);
                let row_pb_low = DeIPA::<P>::interpolate_from_eval_domain(&n_evals.row_pb_low, &x_domain);
                (row_pa_low, row_pa_high, row_pb_low)
            },
            || {
                let row_pb_high = DeIPA::<P>::interpolate_from_eval_domain(&n_evals.row_pb_high, &x_domain);
                let row_pc_low = DeIPA::<P>::interpolate_from_eval_domain(&n_evals.row_pc_low, &x_domain);
                let row_pc_high = DeIPA::<P>::interpolate_from_eval_domain(&n_evals.row_pc_high, &x_domain);
                (row_pb_high, row_pc_low, row_pc_high)
            }, 
            || {
                let col_pa = DeIPA::<P>::interpolate_from_eval_domain(&n_evals.col_pa, &x_domain);
                let col_pb = DeIPA::<P>::interpolate_from_eval_domain(&n_evals.col_pb, &x_domain);
                let col_pc = DeIPA::<P>::interpolate_from_eval_domain(&n_evals.col_pc, &x_domain);
                (col_pa, col_pb, col_pc)
            }
        );
        NPolys { row_pa_low, row_pa_high, row_pb_low, row_pb_high, row_pc_low, row_pc_high, col_pa, col_pb, col_pc}
    }

    pub fn commit_n_polys (
        x_srs: &Vec<P::G1Affine>,
        n_polys: &NPolys<P>,
    ) -> Vec<P::G1> {
        let polys = vec![n_polys.row_pa_low.clone(), n_polys.row_pa_high.clone(), n_polys.row_pb_low.clone(),
            n_polys.row_pb_high.clone(), n_polys.row_pc_low.clone(), n_polys.row_pc_high.clone(), 
            n_polys.col_pa.clone(), n_polys.col_pb.clone(), n_polys.col_pc.clone()];
        
        let coms_n = BatchKZG::<P>::commit(&x_srs, &polys).unwrap();
        coms_n
    }

    pub fn compute_lower_a_b_evals_and_polys (
        sub_prover_id: usize,
        row_index: &Vec<DeRowIndex>,
        col_index: &Vec<DeColIndex>,
        m_domain: &GeneralEvaluationDomain<P::ScalarField>,
        x_domain: &GeneralEvaluationDomain<P::ScalarField>,

    ) -> (DeLowerAandBEvals<P>, DeLowerAandBPolys<P>) {
        let m_prime = m_domain.size();
        let w = x_domain.group_gen();
        let de_row_index = &row_index[sub_prover_id];
        let de_col_index = &col_index[sub_prover_id];
        assert_eq!(de_row_index.row_pa_low.len(), m_prime);
        assert_eq!(de_col_index.col_pa.len(), m_prime);

        let (eval_la_pa_low, eval_la_pa_high): (Vec<P::ScalarField>, Vec<P::ScalarField>) = rayon::join(
            || de_row_index.row_pa_low.par_iter().map(|exp| w.pow([*exp as u64])).collect(),
            || de_row_index.row_pa_high.par_iter().map(|exp| w.pow([*exp as u64])).collect()    
        );

        let (eval_la_pb_low, eval_la_pb_high): (Vec<P::ScalarField>, Vec<P::ScalarField>) = rayon::join(
            || de_row_index.row_pb_low.par_iter().map(|exp| w.pow([*exp as u64])).collect(),
            || de_row_index.row_pb_high.par_iter().map(|exp| w.pow([*exp as u64])).collect()    
        );

        let (eval_la_pc_low, eval_la_pc_high): (Vec<P::ScalarField>, Vec<P::ScalarField>) = rayon::join(
            || de_row_index.row_pc_low.par_iter().map(|exp| w.pow([*exp as u64])).collect(),
            || de_row_index.row_pc_high.par_iter().map(|exp| w.pow([*exp as u64])).collect()    
        );

        let (eval_lb_pa, eval_lb_pb, eval_lb_pc): (Vec<P::ScalarField>, Vec<P::ScalarField>, Vec<P::ScalarField>) = par_join_3!(
            || de_col_index.col_pa.par_iter().map(|exp| w.pow([*exp as u64])).collect(),
            || de_col_index.col_pb.par_iter().map(|exp| w.pow([*exp as u64])).collect(),
            || de_col_index.col_pc.par_iter().map(|exp| w.pow([*exp as u64])).collect()
        );

        let (la_pa_low, la_pa_high) = rayon::join(
            || {
                let eval_domain_la_pa_low = Evaluations::from_vec_and_domain(eval_la_pa_low.clone(), *m_domain);
                eval_domain_la_pa_low.interpolate()
            },
            || {
                let eval_domain_la_pa_high = Evaluations::from_vec_and_domain(eval_la_pa_high.clone(), *m_domain);
                eval_domain_la_pa_high.interpolate()
            }
        );

        let (la_pb_low, la_pb_high) = rayon::join(
            || {
                let eval_domain_la_pb_low = Evaluations::from_vec_and_domain(eval_la_pb_low.clone(), *m_domain);
                eval_domain_la_pb_low.interpolate()
            },
            || {
                let eval_domain_la_pb_high = Evaluations::from_vec_and_domain(eval_la_pb_high.clone(), *m_domain);
                eval_domain_la_pb_high.interpolate()
            }
        );

        let (la_pc_low, la_pc_high) = rayon::join(
            || {
                let eval_domain_la_pc_low = Evaluations::from_vec_and_domain(eval_la_pc_low.clone(), *m_domain);
                eval_domain_la_pc_low.interpolate()
            },
            || {
                let eval_domain_la_pc_high = Evaluations::from_vec_and_domain(eval_la_pc_high.clone(), *m_domain);
                eval_domain_la_pc_high.interpolate()
            }
        );

        let (lb_pa, lb_pb, lb_pc) = par_join_3!(
            || {
                let eval_domain_lb_pa = Evaluations::from_vec_and_domain(eval_lb_pa.clone(), *m_domain);
                eval_domain_lb_pa.interpolate()
            }, 
            || {
                let eval_domain_lb_pb = Evaluations::from_vec_and_domain(eval_lb_pb.clone(), *m_domain);
                eval_domain_lb_pb.interpolate()
            }, 
            || {
                let eval_domain_lb_pc = Evaluations::from_vec_and_domain(eval_lb_pc.clone(), *m_domain);
                eval_domain_lb_pc.interpolate()
            }
        );

        (DeLowerAandBEvals{ eval_la_pa_low, eval_la_pa_high, eval_la_pb_low, eval_la_pb_high, eval_la_pc_low, eval_la_pc_high, eval_lb_pa, eval_lb_pb, eval_lb_pc }, 
            DeLowerAandBPolys {la_pa_low, la_pa_high, la_pb_low, la_pb_high, la_pc_low, la_pc_high, lb_pa, lb_pb, lb_pc})
    }

    pub fn commit_lower_a_b_polys (
        m_powers: &Vec<Vec<P::G1Affine>>,
        de_polys: &Vec<DeLowerAandBPolys<P>>,
    ) -> Vec<P::G1> {
        let x_polys_la_pa_low: Vec<UnivariatePolynomial<P::ScalarField>> = de_polys.par_iter().map(|polys| polys.la_pa_low.clone()).collect();
        let x_polys_la_pa_high = de_polys.par_iter().map(|polys| polys.la_pa_high.clone()).collect();
        let x_polys_la_pb_low = de_polys.par_iter().map(|polys| polys.la_pb_low.clone()).collect();
        let x_polys_la_pb_high = de_polys.par_iter().map(|polys| polys.la_pb_high.clone()).collect();
        let x_polys_la_pc_low = de_polys.par_iter().map(|polys| polys.la_pc_low.clone()).collect();
        let x_polys_la_pc_high = de_polys.par_iter().map(|polys| polys.la_pc_high.clone()).collect();

        let x_polys_lb_pa = de_polys.par_iter().map(|polys| polys.lb_pa.clone()).collect();
        let x_polys_lb_pb = de_polys.par_iter().map(|polys| polys.lb_pb.clone()).collect();
        let x_polys_lb_pc = de_polys.par_iter().map(|polys| polys.lb_pc.clone()).collect();

        let biv_la_pa_low = BivariatePolynomial {x_polynomials: x_polys_la_pa_low};
        let biv_la_pa_high = BivariatePolynomial {x_polynomials: x_polys_la_pa_high};
        let biv_la_pb_low = BivariatePolynomial {x_polynomials: x_polys_la_pb_low};
        let biv_la_pb_high = BivariatePolynomial {x_polynomials: x_polys_la_pb_high};
        let biv_la_pc_low = BivariatePolynomial {x_polynomials: x_polys_la_pc_low};
        let biv_la_pc_high = BivariatePolynomial {x_polynomials: x_polys_la_pc_high};

        let biv_lb_pa = BivariatePolynomial {x_polynomials: x_polys_lb_pa};
        let biv_lb_pb = BivariatePolynomial {x_polynomials: x_polys_lb_pb};
        let biv_lb_pc = BivariatePolynomial {x_polynomials: x_polys_lb_pc};

        let biv_polys = vec![biv_la_pa_low, biv_la_pa_high, biv_la_pb_low, biv_la_pb_high, biv_la_pc_low, biv_la_pc_high, biv_lb_pa, biv_lb_pb, biv_lb_pc];
        // let total_x_polys = vec![x_polys_la_pa_low, x_polys_la_pa_high, x_polys_la_pb_low, x_polys_la_pb_high,
        //                                         x_polys_la_pc_low, x_polys_la_pc_high, x_polys_lb_pa, x_polys_lb_pb, x_polys_lb_pc];
        // let coms: Vec<P::G1> = total_x_polys.par_iter().map(|x_polys| {
        //     x_polys.par_iter().zip(m_powers.par_iter()).map(|(poly, power)|{
        //         let mut coeffs = poly.coeffs.to_vec();
        //         coeffs.resize(power.len(), <P::ScalarField>::zero());
        //         P::G1::msm(&power, &coeffs).unwrap()
        //     }).sum()
        // }).collect();
        let coms = BivBatchKZG::<P>::commit(&m_powers, &biv_polys).unwrap();

        coms
    }

    pub fn compute_and_commit_poly_upper_r (
        powers: &Vec<Vec<P::G1Affine>>,
        l: usize,
    ) -> (Vec<UnivariatePolynomial<P::ScalarField>>, P::G1) {
        let x_polynomials: Vec<UnivariatePolynomial<P::ScalarField>> = (0..l).into_par_iter().map(|i| {
            let mut vec = vec![P::ScalarField::zero(); i+1];
            vec[i] = P::ScalarField::one();
            UnivariatePolynomial::from_coefficients_vec(vec)
        }).collect();
        let x_polynomials_res = x_polynomials.clone();

        let biv_poly = BivariatePolynomial{x_polynomials};
        let com = BivariateKZG::<P>::commit(&powers, &biv_poly).unwrap();

        (x_polynomials_res, com)
    }

    // TODO: consider other approaches to be faster
    pub fn commit_poly_upper_l (
        powers: &Vec<Vec<P::G1Affine>>,
        l: usize,
        y_domain: &GeneralEvaluationDomain<P::ScalarField>,
    ) -> P::G1 {
        // use interpolatation to get lagrange polynomials
        let vec = vec![P::ScalarField::zero(); l];
        let x_polynomials: Vec<UnivariatePolynomial<P::ScalarField>> = (0..l).into_par_iter().map(|i| {
            let mut vec_cur = vec.clone();
            vec_cur[i] = P::ScalarField::one();
            DeIPA::<P>::interpolate_from_eval_domain(&vec_cur, &y_domain)
        }).collect();

        let biv_poly = BivariatePolynomial{x_polynomials};
        let com = BivariateKZG::<P>::commit(&powers, &biv_poly).unwrap();

        com
    }

}
