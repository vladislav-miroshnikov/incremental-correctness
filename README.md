# Coq Formalization: Incremental Type Inference Correctness

This Coq development verifies the **correctness of an incremental type inference strategy** for a Python IDE.

## Goal

To formally prove that **incremental cache invalidation**—clearing the cache only for modified files—is **equivalent** in effect to the traditional baseline strategy that resets all transitively dependent files.

## Key Concepts

- `type`, `file`, `expr`, `name`: abstract entities representing types, source files, expressions, and identifiers.
- `depends`: a transitive, acyclic relation between files.
- `resolve`: resolves a name in a file to its type.
- `cache`: a function mapping `(file, expr)` pairs to optional inferred types.
- `infer`: computes a type for an expression in a file using the cache.

## Core Ideas

- **Baseline strategy** resets all dependent files via transitive dependency analysis.
- **Incremental strategy** resets only the modified file.
- Axioms and lemmas prove that both approaches yield the same inference results.

## Highlights

- `incremental_correct`: formal equivalence between incremental and baseline inference.
- Lemmas showing cache preservation for unrelated files.
- Proof that sequential incremental resets equal full cache reset.

This formalization underpins optimizations in type inference systems and helps ensure correctness in incremental IDE workflows.
