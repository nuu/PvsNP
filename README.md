# MAG: Formalizing P ≠ NP via Group-Theoretic Semantics

A Lean 4 formalization of the **Minimum Asymmetry Gap (MAG)** framework, which translates P vs NP into group theory.

## Overview

MAG provides a group-theoretic semantics where:

| Concept | MAG Translation |
|---------|-----------------|
| **Polytime algorithm** | Solvable group |
| **NP-hard problem** | Non-solvable group (A₅ embedding) |
| **Solves** | Group isomorphism |

The core insight: **solvable groups cannot be isomorphic to non-solvable groups**, yielding P ≠ NP within this semantics.

## Main Results

| Theorem | Description | Status |
|---------|-------------|--------|
| **Theorem 3.1** | MAG internal P ≠ NP | ✅ sorry-free |
| **Theorem 4.6** | A₅ Universal Barrier | ✅ sorry-free |
| **Theorem 4.7** | Solvable vanishing depth | ✅ sorry-free |
| **Theorem 5.4** | Bridge theorem (conditional) | ✅ sorry-free |
| **Theorem 5.7** | Toy model verification | ✅ sorry-free |

## Building

```bash
# Build core theorems (default)
lake build

# Build support modules
lake build Support

# Build all (including blueprints)
lake build MAG
```

## Requirements

- Lean 4.27.0-rc1
- Mathlib

## Scope

This formalization does **NOT** unconditionally claim to solve the Clay P vs NP problem.

- **Unconditional:** MAG-internal P ≠ NP (group-theoretic definitions)
- **Conditional:** If `TranslationInterface` holds, then standard P ≠ NP

## Historical Foundation

MAG synthesizes:
- **Galois (1832):** Solvability concept
- **Klein (1872):** Erlangen Program methodology
- **Krohn-Rhodes (1965):** Automata decomposition
- **Barrington (1986):** NC¹ = width-5 BP over S₅
- **CFSG:** A₅ as minimal non-solvable simple group

## License

MIT License

## Author

Masaru Numagaki, January 2026
