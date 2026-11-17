# Vendored third-party library: `pontryagin`

This directory contains a third-party Lean library. It is **not** the work of Wayne Lewis and is
not part of the AdelicTori formalization proper.

| | |
|---|---|
| Upstream | https://github.com/shosonoda/pontryagin |
| Upstream commit | `4f72437124104369dc18ac380061bc2006f8e392` (2026-07-23) |
| Authors | The pontryagin contributors (see the copyright header of each file) |
| License | Apache License 2.0 (`LICENSE` in this directory, copied unchanged from upstream) |
| Upstream README | `UPSTREAM_README.md`, copied unchanged |
| Upstream toolchain | Lean / Mathlib `v4.32.0` |
| Toolchain here | Lean / Mathlib `v4.34.0-rc2` |

Content: Pontryagin duality for locally compact Hausdorff abelian groups,
`PontryaginDual.toDoubleDual : G ≃ₜ* PontryaginDual (PontryaginDual G)` with
`toDoubleDual G g χ = χ g`, proved via the L¹ group algebra, Gelfand spectrum, Bochner's
theorem, the dual Haar measure, Fourier inversion and Plancherel.

Only the library `Pontryagin/` and `Pontryagin.lean` were copied. Upstream's `Challenge.lean`,
`Solution.lean`, `blueprint/`, `data/`, `PLAN.md` and `UPSTREAMING.md` were not copied.

## Verification before porting

At the upstream commit and toolchain, in an isolated checkout with its own Mathlib cache:
`lake exe cache get`, `lake build Pontryagin Solution`, and `#print axioms` all succeeded.
`pontryagin_duality`, `PontryaginDual.toDoubleDual` and `PontryaginDual.eval_injective` depend
only on `propext`, `Classical.choice`, `Quot.sound`.

## Modifications made for Lean / Mathlib v4.34.0-rc2

No theorem statement or definition was changed. All edits are to proofs or imports.

1. `Pontryagin/Mathlib/FiniteMeasureFubini.lean`, line 1: added
   `import Mathlib.MeasureTheory.Integral.DominatedConvergence`
   (`tendsto_integral_of_dominated_convergence` moved to that file in Mathlib).
2. `Pontryagin/PositiveType.lean`, line 226:
   `by simp` → `by simpa using (Circle.norm_coe (χ z)).le`
3. `Pontryagin/Bochner.lean`, line 1164: the same replacement.
4. `Pontryagin/Inversion.lean`, line 181: the same replacement, with `χ x`.
5. `Pontryagin/Inversion.lean`, line 189: the same replacement, with `χ x`.

Edits 2–5: under v4.34's stricter transparency, `simp` no longer rewrites the norm of the
coercion `Circle → ℂ`; the bound `‖(χ z : ℂ)‖ ≤ 1` is now supplied by `Circle.norm_coe`.

## Lake configuration

The root `lakefile.toml` declares this library as `[[lean_lib]] name = "Pontryagin"` with
`srcDir = "vendor/Pontryagin"` and upstream's `leanOptions`, **scoped to this library only**:

```toml
leanOptions = { pp.unicode.fun = true, relaxedAutoImplicit = false,
                weak.linter.mathlibStandardSet = true, maxSynthPendingDepth = 3 }
```

`maxSynthPendingDepth = 3` is required (without it `L1Algebra.lean` fails instance search). The
AdelicTori library itself is built with default options.
