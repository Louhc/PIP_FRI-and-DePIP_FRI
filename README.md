<h1 align="center">Soloist (Distributed SNARKs for Rank-1 Constraint System)</h1>

This is a Rust library for ___Soloist___, a distributed SNARK for R1CS with constant proof size, constant verifier complexity, and constant amortized communication complexity.
This library also includes implementations and benchmarks of the underlying sub-protocols, such as an improved inner product argument with constant proof size from univariate sum-check and coefficient-based polynomials, and a bivariate batch KZG PCS first supporting multiple polynomials and multiple points.

**WARNING:** This is an academic proof-of-concept prototype, and in particular has not received careful code review. This implementation is NOT ready for production use.

## Metholodgy

The library is implementated based on [arkworks-rs](https://github.com/arkworks-rs), including the finite fields, polynomials over finite fields, bilinear-pairing groups, and operations over them such as pairing, multi-scalar exponentiations, and fast Fourier transforms.
We choose the Bls12-381 or BN254 curves for fair comparison with other schemes.
Note that operations on BN254, especially multi-scalar exponentiations, can be faster than those on Bls12-381, but the provided security is worse.
We use [merlin](https://merlin.cool/) to implement the Fiat-Shamir transformation.

## Build guide

The library compiles on the `nightly` toolchain of the Rust compiler. To install the latest version of Rust, first install `rustup` by following the instructions [here](https://rustup.rs/), or via your platform's package manager. Once `rustup` is installed, install the Rust toolchain by invoking:
```bash
rustup install nightly
```

After that, clone the library and use `cargo` to build the library:
```bash
cargo build
```

## Benchmarks of non-distributed schemes

The libary comes with benchmarks for inner product arguments and batch bivariate KZG with the same evaluation points on the $Y$-dimension.

To run our IPA and see a performance comparison of IPAs from univariate sum-check in [Marlin](https://eprint.iacr.org/2019/1047) and Larent polynomials in [Dark](https://eprint.iacr.org/2019/1229), invoke:
```
cargo bench --bench my_ipa 
```
The results show the prover time, verifier time, and proof size of these IPAs.

To run the batch bivariate KZG, invoke: 
```
cargo bench --bench biv_batch_kzg
```
It shows the prover time, verifier time, and proof size of our batch bivariaet KZG and directly running the bivariate KZG in [PST13](https://eprint.iacr.org/2011/587.pdf) for multiple times.

## Benchmarks of distributed schemes

The library provides distributed schemes, including the distributed batch bivariate KZG, on random double-dimension points or on random points with the same point over the $Y$ dimension, the distributed SNARK with linear verifier, and the distributed SNARK with constant verifier complexity via preprocessing.

For these distributed schemes, we provide local tests to simulate the distributed network to guarantee the reproducibility.
We utilize 4 sub-provers, which requires the machine with at least 4 cores.

For the distributed batch bivariate KZG, invoke:
```bash
cd kzg

./run_local.sh de_biv_batch_kzg 
```
or the following for the KZG with same point on $Y$-dimension:
```bash
./run_local.sh de_biv_batch_kzg_same_point
```

For the distrbuted SNARK with linear verifier complexity, invoke:
```bash
cd snark   

./run_local.sh snark_nopre
```

For the distrbuted SNARK with constant verifier complexity running over random R1CS, invoke:
```bash
cd snark

./run_local.sh snark_pre
```
For zkRollup transactions, first unzip the r1cs and its witness. We provide 128 sets of random witness.
```bash
cd snark/data

unxz circuit.r1cs.xz 

tar -xJvf witness.tar.xz
```
Then, invoke:
```bash
cd snark

./run_local.sh snark_circom
```
The terminal would print the concrete Setup time, Indexer time, Prover time, Verifeir time, and Proof size.
