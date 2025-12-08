-- UFRF/AlphaDerivation.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UFRF.Params
import UFRF.AlphaNumericBounds  -- <-- new import

namespace UFRF

noncomputable section
open Real

/-- Intrinsic geometric value for α⁻¹ at REST:
    4π³ + π² + π. -/
def alphaIntrinsicInv : ℝ :=
  4 * π ^ 3 + π ^ 2 + π

/--
  Projection correction factor from the UFRF projection law,
  specialized to the atomic→human scale mapping.
-/
def correctionFactor : ℝ :=
  (9 * 311 : ℝ) /
    (312 * (13 : ℝ) ^ 2 * sqrt phi * (137 : ℝ) ^ 2)

/-- Projected (observed) α⁻¹ from UFRF: intrinsic × (1 − correctionFactor). -/
def alphaProjInv : ℝ :=
  alphaIntrinsicInv * (1 - correctionFactor)

/-- Experimental α⁻¹ (CODATA / Morel et al. 2020). -/
def alphaExpInv : ℝ :=
  137.035999084

/-- Absolute error between UFRF projected α⁻¹ and experiment. -/
def absError : ℝ :=
  |alphaProjInv - alphaExpInv|

/-- Error in parts per billion (ppb). -/
def ppbError : ℝ :=
  absError / alphaExpInv * (1e9)

/-
  The axiom is gone.

  Instead, we *import* a theorem proved in `AlphaNumericBounds.lean`:

  theorem alpha_ppb_bound : ppbError ≤ 0.0075
-/

/-- Convenience corollary: we are well within 1σ experimental uncertainty. -/
lemma alpha_within_experimental_sigma :
    ppbError ≤ 0.081 := by
  have h0 : (0.0075 : ℝ) ≤ 0.081 := by
    norm_num
  exact le_trans alpha_ppb_bound h0

end
