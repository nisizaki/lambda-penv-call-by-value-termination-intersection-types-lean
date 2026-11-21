# Call-by-Value Termination of λpenv and its Characterization by Intersection Types (Lean 4)

Lean 4 formalization accompanying the paper

> Shin-ya Nishizaki and Shogo Murasaki.
> *Call-by-Value Termination of λpenv, a Calculus Mixing Functions and Environments, and
> its Characterization by Intersection Types, Formalized in Isabelle/HOL.*

The paper's primary formalization is in Isabelle/HOL
(<https://github.com/nisizaki/lambda-penv-call-by-value-termination-intersection-types>).
This repository is a port of that development to Lean 4. It has one Lean file per
Isabelle theory, with the same definitions and theorem names.

## Main results

```lean
theorem main_characterization    : Typ M ↔ CFN M
theorem main_characterization_SN : Typ M ↔ CFSN M
theorem Typ_imp_SN               : Typ M → SN_at cbv M
theorem clash_not_Typ            : NF M → ¬ fb M → ¬ Typ M
theorem sorted_cbv_iff           : tm M ∨ en M → (cbv M N ↔ cbv0 M N)
theorem conservative_Typ         : tm M → (Typ M ↔ CFN0 M)
theorem conservativity           : pure M → (Typ M ↔ lam_VN (rb M DVar)) ∧ (lam_VN (rb M DVar) ↔ CFSN M)
```

All 15 Isabelle theories are ported.
- There is no `sorry`, `axiom` or `native_decide`.
- `#print axioms` for the main theorems reports only `propext`, `Classical.choice` and
  `Quot.sound`.
- `autoImplicit` is disabled.

## Adaptations

- Sets of terms become predicates, and `rtranclp` becomes `Star`.
- The constructors `Id`, `Extn`, `Comp` and `Nm` become `iden`, `extn`, `comp` and `nm`.
  The types `ty`, `sub` and `hasty` become `Ty`, `Sub` (`≼`) and `Hasty` (`⊢`).
- Isabelle's `inductive inert and fb` becomes a Lean `mutual` pair of inductive types.
- In `Sub`, the rule `s_env` is a theorem. The constructor `s_env_core` splits its
  existential premise into two; this is equivalent because `map_of` is functional.
- `snf` (the σ-normal form) uses `Classical.choose` instead of Isabelle's `SOME`.

Authors: Shin-ya Nishizaki and Shogo Murasaki.

## Building

Requires Lean 4 v4.33.1, which `elan` installs automatically from `lean-toolchain`.
There are no dependencies beyond the Lean core library (no Mathlib).

```bash
lake build
```

## Files

```
lean-toolchain, lakefile.toml, lake-manifest.json   Lake project (Lean v4.33.1, no dependencies)
LambdaPEnvCBV.lean                                    root module importing all files
LambdaPEnvCBV/*.lean                                  one file per Isabelle theory (15 files)
```

## Related repositories

- Isabelle/HOL original of this development:
  [lambda-penv-call-by-value-termination-intersection-types](https://github.com/nisizaki/lambda-penv-call-by-value-termination-intersection-types)
- Call-by-name λpenv:
  [lambda-penv-weak-head-normalizability-intersection-types](https://github.com/nisizaki/lambda-penv-weak-head-normalizability-intersection-types)
  ([Lean 4](https://github.com/nisizaki/lambda-penv-weak-head-normalizability-intersection-types-lean))
- The corresponding λenv development:
  [lambda-env-call-by-value-termination-intersection-types](https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types)
  ([Lean 4](https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types-lean))
- λpenv and the confluence of its weak reduction:
  [lambda-penv-confluence-public](https://github.com/nisizaki/lambda-penv-confluence-public)

## How to cite

Cite the paper quoted at the top of this file.
