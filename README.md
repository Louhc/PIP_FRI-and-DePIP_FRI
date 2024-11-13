<h1 align="center">District1 (Distributed R1CS-Targeted SNARKs)</h1>

___District1___ is a Rust library for a distributed SNARK for R1CS with constant proof size, constant verifier complexity, and constant amortized communication complexity.
It also includes various implementations which may of independent interests, such as an improved inner product argument with constant proof size following the "Polynomial interactive oracle proof (PIOP) + Polynomial commitment scheme (PCS)" approach, and a bivariate batch KZG PCS first supporting multiple polynomials and points.

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
To run our IPA and see a performance comparison of IPAs from univariate sum-check and Larent polynomials, invoke:
```
cargo bench --bench my_ipa 
```
The results show the prover time, verifier time, and proof size of these IPAs.

To run the batch bivariate KZG, invoke: 
```
cargo bench --bench biv_batch_kzg
```
It shows the prover time, verifier time, and proof size of running the trivial bivariate KZG multiple times and our batch bivariate KZG.

## Benchmarks of distributed schemes

The library provides distributed schemes, including the distributed batch bivariate KZG, on random double-dimension points or on random points with the same point over the $Y$ dimension, the distributed SNARK with linear verifier, and the distributed SNARK with constant verifier complexity via preprocessing.

For these distributed schemes, we provide local tests to simulate the distributed network to guarantee the reproducibility using 4 cores.

For the distributed batch bivariate KZG, invoke:
```bash
cd kzg

RAYON_NUM_THREADS=N RUSTFLAGS='-C target-cpu=native' cargo build --release --example de_biv_batch_kzg --no-default-features --features "parallel asm"    

./run_local.sh de_biv_batch_kzg 
```
or 
```bash
./run_local.sh de_biv_batch_kzg_same_point
```
where $N=4$, and also for the $N$ 's below.

For the distrbuted SNARK with linear verifier complexity, invoke:
```bash
cd snark

RAYON_NUM_THREADS=N RUSTFLAGS='-C target-cpu=native' cargo build --release --example snark_nopre --no-default-features --features "parallel asm"    

./run_local.sh snark_nopre
```

For the distrbuted SNARK with constant verifier complexity, invoke:
```bash
cd snark

RAYON_NUM_THREADS=N RUSTFLAGS='-C target-cpu=native' cargo build --release --example snark_pre --no-default-features --features "parallel asm"    

./run_local.sh snark_pre
```


