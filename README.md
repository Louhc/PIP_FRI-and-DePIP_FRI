<h1 align="center">PIP<sub>FRI</sub>: Shred-to-Shine Metamorphosis in Polynomial Commitment</h1>

This is a Rust library for ___PIP<sub>FRI</sub>___, an efficient FRI/RS-based zero-knowledge multilinear polynomial commitment scheme.

## Overview

This repository facilitates benchmarking tests for PIP<sub>FRI</sub> built on the implementations of [PolyFRIM](https://github.com/guo-yanpei/PolyFRIM) (USENIX Security 24) and [Deepfold](https://github.com/guo-yanpei/deepfold-bench) (USENIX Security 25).
Different from their implementations, we use the `arkworks` ecosystem for finite fields and polynomial operations.

## Implementation details

- **Field and hash**: 
The field is $\mathbb{F}_{p}$ where $p = 2^{64} - 2^{32} + 1$, i.e., the Goldilocks field.
It is feasible to change it following the arkworks.
We use the [$\mathsf{rs}\_\mathsf{merkle}$](https://docs.rs/rs_merkle/latest/rs_merkle) package to build Merkle trees.
We use the hash function Blake3 with output size of 256 bits. 

- **FRI details**: 
The chosen code rate is $2^{-3}$.
The security level is 100 bit.
The soundness choice is the conjectured one, same as implemenations like [plonky2](https://github.com/0xPolygonZero/plonky2) and [estark](https://ia.cr/2021/582).
To modify these parameters, adjust the `SECURITY_BITS` and `CODE_RATE` in [utils](utils/src/lib.rs).
We do not use the grinding technique, also know as the proof-of-work technique.
We reduce the polynomial degree stricly by half in each round until a constant.

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

## PCS Benchmarks
  
- **Benchmark a Specific PCS**: Choose from `fri`, `virgo`, `polyfrim`, `deepfold` or `pip_fri`.
  ```bash
  cargo bench -p <protocol>
  ```

### Virgo GKR

For the multilinear polynomial commitment scheme in Virgo, there's an included GKR.

**Benchmarking GKR**:
1. Execute `bench_gkr.py` within the `virgo/` directory.
2. This script calls the executable `virgo/fft_gkr` and produces the GKR prover time, verifier time, and proof size.

> **Note**: The executable originates from [Virgo](https://github.com/sunblaze-ucb/Virgo), and we're directly utilizing it here.

For the final evaluation result of Virgo, it's essential to sum the results from the Rust implementation and the GKR. This summation is a manual process.


## Distributed PCS benchmarks

For the distributed PCS, modify the `variable_num` in [de_pip_fri.rs](de_pip_fri/examples/de_pip_fri.rs) for polynomial size.
Then, run

  ```
  cd de_pip_fri
  ./run_benchmark.sh <sub-prover number> <running times>
  ```

  The sub-prover number should be power of two.