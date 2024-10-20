use ark_poly::{univariate::DensePolynomial as UnivariatePolynomial, 
    // DenseUVPolynomial, 
    EvaluationDomain, Evaluations, GeneralEvaluationDomain, 
    // Polynomial
};
use std::marker::PhantomData;
use ark_ec::{pairing::Pairing, VariableBaseMSM};
use my_kzg::{
    // biv_batch_kzg::BivBatchKZG, biv_trivial_kzg::VerifierSRS, helper::linear_combination_field, 
    par_join_3, 
    // transcript::ProofTranscript, trivial_kzg::{UniVerifierSRS, KZG}, uni_batch_kzg::BatchKZG, uni_trivial_kzg::KZG
};
// use merlin::Transcript;
// use my_ipa::helper::{R1CSPublicPolys, R1CSWitnessPolys, R1CSDePublicPolys};
use ark_ff::{Zero, Field};
// use de_network::{DeMultiNet as Net, DeNet, DeSerNet};
use rayon::prelude::*;
use crate::prover_pre::{DeValPolys, DeRowIndex, DeColIndex};

#[derive(Clone)]
pub struct DeLowerAandBEvals<P: Pairing> {
    pub eval_la_pa_low: Vec<P::ScalarField>,
    pub eval_la_pa_high: Vec<P::ScalarField>,
    pub eval_la_pb_low: Vec<P::ScalarField>,
    pub eval_la_pb_high: Vec<P::ScalarField>,
    pub eval_la_pc_low: Vec<P::ScalarField>,
    pub eval_la_pc_high: Vec<P::ScalarField>,
    pub eval_lb_pa: Vec<P::ScalarField>,
    pub eval_lb_pb: Vec<P::ScalarField>,
    pub eval_lb_pc: Vec<P::ScalarField>,
}

#[derive(Clone)]
pub struct DeLowerAandBPolys<P: Pairing> {
    pub la_pa_low: UnivariatePolynomial<P::ScalarField>,
    pub la_pa_high: UnivariatePolynomial<P::ScalarField>,
    pub la_pb_low: UnivariatePolynomial<P::ScalarField>,
    pub la_pb_high: UnivariatePolynomial<P::ScalarField>,
    pub la_pc_low: UnivariatePolynomial<P::ScalarField>,
    pub la_pc_high: UnivariatePolynomial<P::ScalarField>,
    pub lb_pa: UnivariatePolynomial<P::ScalarField>,
    pub lb_pb: UnivariatePolynomial<P::ScalarField>,
    pub lb_pc: UnivariatePolynomial<P::ScalarField>,
}

#[derive(Clone)]
// The original data of val values
pub struct DeValEvals<P: Pairing> {
    pub eval_val_pa: Vec<P::ScalarField>,
    pub eval_val_pb: Vec<P::ScalarField>,
    pub eval_val_pc: Vec<P::ScalarField>,
}

pub struct Indexer<P: Pairing> {
    _pairing: PhantomData<P>,
}

impl<P: Pairing> Indexer<P> {

    pub fn compute_val_polys (
        m_domain: &GeneralEvaluationDomain<P::ScalarField>,
        val_evals: &DeValEvals<P>,
    ) -> DeValPolys<P> {
        let (val_pa, val_pb, val_pc) = par_join_3!(
            || {
                let eval_domain_val_pa = Evaluations::<P::ScalarField>::from_vec_and_domain(val_evals.eval_val_pa.clone(), *m_domain);
                eval_domain_val_pa.interpolate()
            },
            || {
                let eval_domain_val_pb = Evaluations::<P::ScalarField>::from_vec_and_domain(val_evals.eval_val_pb.clone(), *m_domain);
                eval_domain_val_pb.interpolate()
            }, 
            || {
                let eval_domain_val_pc = Evaluations::<P::ScalarField>::from_vec_and_domain(val_evals.eval_val_pc.clone(), *m_domain);
                eval_domain_val_pc.interpolate()
            }
        );
        DeValPolys { val_pa, val_pb, val_pc}
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
        powers: &Vec<Vec<P::G1Affine>>,
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

        let total_x_polys = vec![x_polys_la_pa_low, x_polys_la_pa_high, x_polys_la_pb_low, x_polys_la_pb_high,
                                                x_polys_la_pc_low, x_polys_la_pc_high, x_polys_lb_pa, x_polys_lb_pb, x_polys_lb_pc];
        let coms: Vec<P::G1> = total_x_polys.par_iter().map(|x_polys| {
            x_polys.par_iter().zip(powers.par_iter()).map(|(poly, power)|{
                let mut coeffs = poly.coeffs.to_vec();
                coeffs.resize(power.len(), <P::ScalarField>::zero());
                P::G1::msm(&power, &coeffs).unwrap()
            }).sum()
        }).collect();

        coms
    }
}
