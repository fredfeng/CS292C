# Final Track A: Automated Bug Detection for zkVM Systems

## Project Background

Zero-Knowledge Virtual Machines (zkVMs), such as OpenVM [1] and SP1 [2], represent an emerging class of infrastructure for verifiable computation. These systems are actively evolving and, like any complex software, may contain bugs—ranging from minor correctness issues to serious logical or security flaws. Building automated techniques to detect such bugs offers both a rewarding technical challenge and tangible contributions to real-world systems.

A zkVM is a virtual machine that executes programs while generating cryptographic proofs that attest to their correct execution. These proofs can be independently verified without rerunning the original computation, ensuring strong guarantees of integrity and privacy. zkVMs are particularly valuable in blockchain and decentralized environments, where trustless verification is essential. They typically lower high-level programs into arithmetic circuits suitable for proving systems such as SNARKs or STARKs.

## Motivating Example

Consider a simple OpenVM program that computes the nth Fibonacci number (check out more of the detail at the OpenVM book):

```rust
// src/main.rs
use openvm::io::{read, reveal_u32};

fn main() {
    let n: u64 = read();
    let mut a: u64 = 0;
    let mut b: u64 = 1;
    for _ in 0..n {
        let c: u64 = a.wrapping_add(b);
        a = b;
        b = c;
    }
    reveal_u32(a as u32, 0);
    reveal_u32((a >> 32) as u32, 1);
}
```

If the loop is mistakenly written as `for _ in 0..=n`, the output becomes `F(n+1)` rather than `F(n)`. The program runs successfully and emits an output—but the semantics are subtly incorrect.

Though simple, this kind of off-by-one bug has appeared in production systems. For instance, in April 2025, Scroll’s mainnet experienced a critical vulnerability stemming from a similar loop boundary error in a zkVM circuit, which allowed malformed proofs to be incorrectly accepted. The issue required an emergency upgrade. You may check out the incident report [5].

Such bugs are difficult to detect through conventional testing. zkVM proofs confirm that a given circuit was executed correctly—but not that the circuit’s logic matches the developer’s intent. This semantic gap underscores the need for formal specifications and verification tools that can catch these high-impact discrepancies.

## Goal, Scope and Benchmarks

This project invites you to design and prototype a tool that uses formal methods to detect real-world bugs in zkVM implementations, in particular for OpenVM [1] and SP1 [2]. You’ll focus on issues reported in their audit logs, particularly those marked as *medium severity or higher*:

- OpenVM Audit Reports [3]
- SP1 Audit Reports [4]

Your tool does not need to detect every issue listed. Instead, aim to:

- Address a few concrete bugs from the audits (e.g., 2–3 specific entries), or
- Target one or more broader classes of issues (e.g., data validation errors, access control bugs, or logic mismatches).

Your solution can be scoped appropriately to the course timeline, but it should demonstrate a rigorous formal reasoning approach and evidence of practical applicability.

## Approaches

We strongly encourage projects to adopt formal verification methods as the primary approach. This includes using model checkers, proof assistants, or domain-specific verification techniques to express and prove correctness properties relevant to zkVM execution.

While other approaches—such as static analysis or fuzzing—are also acceptable, they should be used with care. For instance, static analysis techniques must account for potential false positives, and fuzzing-based solutions should include strategies to address scalability and completeness limitations. In all cases, your rationale should be clearly articulated, and your methodology should aim for clarity, soundness, and relevance to real bugs identified in the audit reports.

This project is an opportunity to apply your knowledge of formal methods to an impactful and technically rich domain. Strong submissions will demonstrate thoughtful problem selection, sound formal reasoning, and a working prototype that illustrates the potential of your approach.

## Frameworks (Feel free to use other options)

- Flux: https://flux-rs.github.io/flux/
- MIRAI (Facebook): Abstract-interpretation static analyzer for Rust MIR: https://github.com/facebookexperimental/MIRAI
- Crux-MIR (Galois): Symbolic execution of Rust MIR with path exploration: https://tools.galois.com/saw/crux/what-is-crux
- haybale (LLVM symbolic executor in Rust): Lightweight, supports concrete+symbolic (“concolic”) execution of Rust binaries; https://github.com/PLSysSec/haybale

## Resources

[1] OpenVM: [https://github.com/openvm-org/openvm](https://github.com/openvm-org/openvm)

[2] SP1: [https://github.com/succinctlabs/sp1](https://github.com/succinctlabs/sp1)

[3] OpenVM Audit Reports: [https://github.com/openvm-org/openvm/tree/main/audits](https://github.com/openvm-org/openvm/tree/main/audits); in particular, the following reports are good starting points:

- [https://github.com/openvm-org/openvm/blob/main/audits/v1-cantina-report.pdf](https://github.com/openvm-org/openvm/blob/main/audits/v1-cantina-report.pdf)
- [https://github.com/openvm-org/openvm/tree/main/audits/v1-internal](https://github.com/openvm-org/openvm/tree/main/audits/v1-internal)

[4] SP1 Audit Reports: [https://github.com/succinctlabs/sp1/tree/dev/audits](https://github.com/succinctlabs/sp1/tree/dev/audits); in particular, the following reports are good starting points:

- [https://github.com/succinctlabs/sp1/blob/dev/audits/cantina.pdf](https://github.com/succinctlabs/sp1/blob/dev/audits/cantina.pdf)
- [https://github.com/succinctlabs/sp1/blob/dev/audits/veridise.pdf](https://github.com/succinctlabs/sp1/blob/dev/audits/veridise.pdf)

[5] Scroll Incident Report for Mainnet Emergency Upgrade on 2025-04-25: [https://forum.scroll.io/t/report-scroll-mainnet-emergency-upgrade-on-2025-04-25/666](https://forum.scroll.io/t/report-scroll-mainnet-emergency-upgrade-on-2025-04-25/666)

[6] OpenVM Book: [https://book.openvm.dev/](https://book.openvm.dev/)

[7] SP1 Docs: [https://docs.succinct.xyz/docs/sp1/introduction](https://docs.succinct.xyz/docs/sp1/introduction)
