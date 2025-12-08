-- lean/UFRF/Moonshine.lean
/-
UFRF Moonshine Parametric Layer

Author: Daniel Charboneau

This file provides a Params-aware wrapper around the Monster Moonshine coefficients.
It proves that jCoeff and B2 are independent of which Params instance you use,
once the axioms hold (via params_unique).
-/

import UFRF.Params
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic

import MonsterMoonshineUFRF.Monster_Moonshine

namespace UFRF

open MonsterMoonshineUFRF

-- Access monster_coeff and B2 from Monster_Moonshine.lean
-- They are defined in the UFRF namespace there
def jCoeff (A : Params) (n : ℤ) : ℤ :=
  Monster_Moonshine.monster_coeff n

/--
Parametrized B₂ constant.

Hooked directly to your `B2`.
-/
def B2 (A : Params) : ℝ :=
  Monster_Moonshine.B2

/-! ### Local value theorems, restated with Params -/

lemma jCoeff_neg_one (A : Params) :
  jCoeff A (-1) = 1 := by
  simpa [jCoeff] using (by simp [Monster_Moonshine.monster_coeff] : Monster_Moonshine.monster_coeff (-1) = 1)

lemma jCoeff_zero (A : Params) :
  jCoeff A 0 = 0 := by
  simpa [jCoeff] using (by simp [Monster_Moonshine.monster_coeff] : Monster_Moonshine.monster_coeff 0 = 0)

lemma jCoeff_one (A : Params) :
  jCoeff A 1 = 196884 := by
  simpa [jCoeff] using (by simp [Monster_Moonshine.monster_coeff] : Monster_Moonshine.monster_coeff 1 = 196884)

lemma B2_value (A : Params) :
  B2 A = 196884 * 169 / (744 * 60) := by
  simp [B2, Monster_Moonshine.B2]
  -- B2 from Monster_Moonshine is defined as this value
  rfl

/-! ### No-free-parameter invariance theorems -/

/-- jCoeff is independent of which Params you pick, once axioms hold. -/
theorem jCoeff_param_invariant (A₁ A₂ : Params) (n : ℤ) :
  jCoeff A₁ n = jCoeff A₂ n := by
  -- right now jCoeff ignores A, so this is trivial,
  -- but we phrase it via params_unique so the theorem
  -- survives future refactors.
  have h₁ : A₁ = Params.canonical := Params.params_unique A₁
  have h₂ : A₂ = Params.canonical := Params.params_unique A₂
  simp [jCoeff, h₁, h₂]

/-- B₂ is independent of Params. -/
theorem B2_param_invariant (A₁ A₂ : Params) :
  B2 A₁ = B2 A₂ := by
  have h₁ : A₁ = Params.canonical := Params.params_unique A₁
  have h₂ : A₂ = Params.canonical := Params.params_unique A₂
  simp [B2, h₁, h₂]

/-- Concrete value of B₂ for canonical Params. -/
theorem B2_canonical :
  B2 Params.canonical = 196884 * 169 / (744 * 60) := by
  simpa using B2_value Params.canonical

/--
Main "no free parameters" statement for B₂:

for ANY UFRF.Params satisfying the axioms, B₂ must be 196884 * 169 / (744 * 60).
-/
theorem B2_for_all_params (A : Params) :
  B2 A = 196884 * 169 / (744 * 60) := by
  have h : B2 A = B2 Params.canonical :=
    B2_param_invariant A Params.canonical
  simpa [B2_canonical] using h

/--
Example: jCoeff(1) is 196884 for any admissible UFRF.Params.
-/
theorem jCoeff_one_for_all (A : Params) :
  jCoeff A 1 = 196884 := by
  have h : jCoeff A 1 = jCoeff Params.canonical 1 :=
    jCoeff_param_invariant A Params.canonical 1
  have h_can : jCoeff Params.canonical 1 = 196884 :=
    jCoeff_one Params.canonical
  exact h.trans h_can

end UFRF

