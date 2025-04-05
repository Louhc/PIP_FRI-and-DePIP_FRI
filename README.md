<h1 align="center">PIP<sub>FRI</sub>: Shred-to-Shine Metamorphosis in Polynomial Commitment</h1>

This is a Rust library for ___PIP<sub>FRI</sub>___, an efficient FRI/RS-based zero-knowledge multilinear polynomial commitment scheme.

 distributed SNARK for R1CS with constant proof size, constant verifier complexity, and constant amortized communication complexity.
This library also includes implementations and benchmarks of the underlying sub-protocols, such as an improved inner product argument with constant proof size from univariate sum-check and coefficient-based polynomials, and a bivariate batch KZG PCS first supporting multiple polynomials and multiple points.

## Overview

This repository facilitates benchmarking tests for PIP<sub>FRI</sub> built on the implementations of [PolyFRIM/FRISS](https://github.com/gyp2847399255/PolyFRIM) (USENIX Security 24), [Brakedown](https://github.com/conroi/lcpc) (CRYPTO 23), and [Spartan](https://github.com/Microsoft/Spartan) (CRYPTO 20).

### Implementation details

- **Field and hash**: 
The field compared with RS-based schemes is $\mathbb{F}_{p^2}$ from PolyFRIM, adopted from [Virgo](https://github.com/sunblaze-ucb/Virgo) (S\&P 20), with $\mathbb{F}_{p}$ where $p = 2^{61} - 1$ as the base field.
The field compared with GS-based schemes is 255 bit field from Brakedown.
We use Blake3 with output size of 256 bits as the hash function. 

- **FRI details**: 
The chosen code rate is $2^{-3}$.
The security level is 120 bit.
The soundness choice is the conjectured one, same as implemenations like [plonky2](https://github.com/0xPolygonZero/plonky2) and [estark](https://ia.cr/2021/582).
To modify these parameters, adjust the `SECURITY_BITS`, `CODE_RATE`, and query number in [utl](pcs/src/lib.rs).
We do not use the grinding technique, and reduce the polynomial degree stricly by half in each round until a constant, different from optimizations like in plonky2 and estark.


### Provided Implementations
  - **PIP<sub>FRI</sub>**: The multi-linear FRI-based polynomial commitment scheme proposed in paper. Find this mainly in the `pcs/` directory.

  - **Other FRI-based Univariate/Multilinear polynomial commitments**: Include FRI-PCS in `fri/`, Virgo in `virgo/`, Gemini (or HyperPlonk) in `gemini-fri/`, Basefold-RS in `basefold/`, and PolyFRIM in `polyfrim/` for comparative purposes.

  - **SNARK**: We implement PIP<sub>SNARK</sub> by combining the PIOP in Spartan and PIP<sub>FRI</sub>.
  Find this in [spartan](/spartan/benches/nizk.rs).
  Same as Orion-SNARK, we only use the linear-verifier version and do not use preprocessing.
  As Orion-PCS is written in C++, to test the performance of Orion-SNARK, we extract the PIOP times of PIP<sub>SNARK</sub> and add them to the Orion-PCS times for SNARK times.

- **Utilities**: All the above protocols leverage utilities found in `util/`, which includes implementations for Merkle trees, finite fields, polynomials, and other necessary tools.

## Setup

1. **Install Rust**: Follow the instructions on [Rust Installation](https://www.rust-lang.org/tools/install).
   
2. **Verify Installation**: Post-installation, ensure everything is set up correctly with:
   ```bash
   cargo --version
   rustup --version
   ```

3. **Use the Nightly Toolchain**: 
   ```bash
   rustup default nightly
   ```

## PCS tests

- **Benchmark All PCSs**: 
  ```bash
  cargo bench
  ```
  
- **Benchmark a Specific PCS**: Choose from `fri`, `virgo`, `gemini-fri`, `basefold`, `polyfrim`, or `pcs`.
  ```bash
  cargo bench -p <protocol>
  ```
  
> **Note**: The most extensive benchmarking point may require approximately 80 GB of RAM.

- **Test All Protocols & Output Proof Sizes**: 
  ```bash
  cargo test -- --nocapture
  ```

- **Test & Output Proof Size for a Specific Protocol**: Choose from `fri`, `virgo`, `gemini-fri`, `basefold`, `polyfrim`, or `pcs`.
  ```bash
  cargo test -p <protocol> -- --nocapture
  ```

### Virgo GKR

For the multi-linear polynomial commitment in Virgo, there's an included GKR.

**Benchmarking GKR**:
1. Execute `bench_gkr.py` within the `virgo/` directory.
2. This script calls the executable `virgo/fft_gkr` and produces the GKR prover time, verifier time, and proof size.

> **Note**: The executable originates from [Virgo](https://github.com/sunblaze-ucb/Virgo), and we're directly utilizing it here.

For the final evaluation result of Virgo, it's essential to sum the results from the Rust implementation and the GKR. This summation is a manual process.

### Other multilinear PCSs

For Brakedown and [Orion](https://github.com/sunblaze-ucb/Orion), we refer to their open-sourced implementations for results.
For query numbers, we follow Lemma 1 in [Brakedown](https://eprint.iacr.org/2021/1043) paper.


## SNARK tests

To see the prover time, verifier time, and proof size, run

  ```
  cd spartan
  cargo build --release --all-features
  ./target/release/nizk
  ```

The `polycommit` is commitment time of polynomial commitment; the `polyeval` is prover time of polynomial commitment.
The `NIZK::prove` time other than PCS commitment and prover time is the prover time of PIOP.
  
The `poly_eva_verify` is verifier time of polynomial commitment.
The verifier time of PIOP can be similarly obatained from `NIZK::verify time`.

The `NIZK::pcs_proof_len` is the proof size of PCS.
The `NIZK::proof_compressed_len` is the total proof size of SNARK.


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

For these distributed schemes, run
```bash
RAYON_NUM_THREADS=N RUSTFLAGS="-C target-cpu=native" cargo build --release --example <protocol_name> --no-default-features --features "parallel asm"
```
on each sub-prover for building, where $N$ is the number of cores for parallelization for each sub-prover.

Then, invoke on each sub-prover
```bash
cd target/release/examples 
./<protocol_name> <id> <file_of_ip>
```

To guarantee the reproducibility, we provide local tests to simulate the distributed network.
For the local tests, we utilize 4 sub-provers, which requires the local machine with at least 4 cores.

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
