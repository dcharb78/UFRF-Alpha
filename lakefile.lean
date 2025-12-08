/-

UFRF Monster Moonshine Proof

============================

This Lean 4 project proves that the Monster group dimension 196884

emerges necessarily from UFRF geometric constraints.



KEY POINT: This is not an isolated mathematical curiosity.

The 13-cycle structure used here is the SAME geometric pattern that:

- Determines nuclear shell gaps (2.5, 5.5, 8.5, 11.5 MeV)

- Derives the fine structure constant (α⁻¹ = 4π³ + π² + π)

- Predicts graphene viscosity-entropy ratios

- Explains musical octave structure



See docs/CROSS_DOMAIN_VALIDATION.md for full evidence.

See docs/DERIVATION_CHAIN.md for why 13 is derived, not arbitrary.

See docs/OBJECTION_HANDLING.md for anticipated critiques.



The combined statistical significance across all domains exceeds

particle physics discovery threshold (p < 1.5 × 10⁻¹³, equivalent to 7.7σ).

-/

import Lake
open Lake DSL

package «MonsterMoonshineUFRF» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0-rc2"

lean_lib «MonsterMoonshineUFRF» where
  roots := #[`Monster_Moonshine, `PhaseLog_Monoid, `Concurrency_BoundedGap, `ZPartition, `UFRF.Params, `UFRF.Moonshine, `UFRF.AlphaDerivation, `UFRF.AlphaNumericBounds, `UFRF.GravityDerivation, `UFRF.GravityNumericBounds]
