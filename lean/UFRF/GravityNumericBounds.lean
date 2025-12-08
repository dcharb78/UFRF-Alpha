-- UFRF/GravityNumericBounds.lean
/-
  Numeric bounds for the UFRF gravitational coupling α_G.

  Goal: prove a coarse but certified bound like:

    theorem alphaG_percent_bound : percentErrorG ≤ 0.3

  meaning the UFRF gravity prediction matches the experimental
  αG⁻¹ to within 0.3% or better.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import UFRF.Params
import UFRF.AlphaDerivation
import UFRF.GravityDerivation
import UFRF.AlphaNumericBounds   -- reuse phi bounds, sqrtPhi bounds, etc.

namespace UFRF

noncomputable section
open Real

/-
  We can reuse phi_bounds and sqrtPhi_bounds from AlphaNumericBounds.

  If you put those in a shared module later (e.g. UFRF/MathBounds.lean),
  just adjust the imports. For now we assume they're available from
  UFRF.AlphaNumericBounds.
-/

/--
  Crude bounds on alphaGIntrinsicInv = alphaIntrinsicInv * metaCycle^kGravity.
-/
lemma alphaGIntrinsicInv_bounds :
    let loIntr := 4 * piLo ^ 3 + piLo ^ 2 + piLo
    let hiIntr := 4 * piHi ^ 3 + piHi ^ 2 + piHi
    let meta := metaCycle
    in
    loIntr * meta ^ kGravity ≤ alphaGIntrinsicInv
    ∧
    alphaGIntrinsicInv ≤ hiIntr * meta ^ kGravity := by
  intros loIntr hiIntr meta
  -- Unfold definitions to expose alphaIntrinsicInv and metaCycle
  unfold alphaGIntrinsicInv
  unfold metaCycle at meta

  -- Reuse EM intrinsic bounds
  have hIntrLo : loIntr ≤ alphaIntrinsicInv := alphaIntrinsicInv_lo
  have hIntrHi : alphaIntrinsicInv ≤ hiIntr := alphaIntrinsicInv_hi

  -- Show meta > 0
  have hMetaPos : (0 : ℝ) < meta := by
    -- meta = (13 : ℝ) ^ 2
    have h13 : (0 : ℝ) < (13 : ℝ) := by norm_num
    have hPow : (0 : ℝ) < (13 : ℝ) ^ (2 : ℕ) := by
      exact pow_pos h13 _
    simpa using hPow

  -- So meta ^ kGravity > 0, hence ≥ 0
  have hMetaPowNonneg : (0 : ℝ) ≤ meta ^ kGravity :=
    le_of_lt (Real.rpow_pos_of_pos hMetaPos kGravity)

  constructor
  · -- lower bound
    have h := mul_le_mul_of_nonneg_right hIntrLo hMetaPowNonneg
    simpa [alphaGIntrinsicInv, metaCycle] using h
  · -- upper bound
    have h := mul_le_mul_of_nonneg_right hIntrHi hMetaPowNonneg
    simpa [alphaGIntrinsicInv, metaCycle] using h

/--
  Bounds on gravityProjection =
    (gravityObserverOffset / (kGravity * √φ)) * gravityScaleRatio.
-/
lemma gravityProjection_bounds :
    let loProj := (gravityObserverOffset / (kGravity * sqrtPhiHi)) * gravityScaleRatio
    let hiProj := (gravityObserverOffset / (kGravity * sqrtPhiLo)) * gravityScaleRatio
    in
    loProj ≤ gravityProjection ∧ gravityProjection ≤ hiProj := by
  intros loProj hiProj
  unfold gravityProjection
  unfold gravityObserverOffset gravityScaleRatio
  have hSqrtPhi := sqrtPhi_bounds
  rcases hSqrtPhi with ⟨hLo, hHi⟩
  -- Since sqrtPhiLo ≤ sqrt phi ≤ sqrtPhiHi, and we're dividing by it,
  -- the fraction (0.5 / (kGravity * sqrt phi)) is:
  --   largest when sqrt phi is smallest (sqrtPhiLo)
  --   smallest when sqrt phi is largest (sqrtPhiHi)
  -- So: (0.5 / (kGravity * sqrtPhiHi)) ≤ (0.5 / (kGravity * sqrt phi)) ≤ (0.5 / (kGravity * sqrtPhiLo))
  constructor
  · -- lower bound: loProj ≤ gravityProjection
    have h_denom : kGravity * sqrtPhiHi ≤ kGravity * sqrt phi := by
      have h_pos : (0 : ℝ) < kGravity := by unfold kGravity; norm_num
      apply mul_le_mul_of_nonneg_left hHi h_pos
    have h_frac : (0.5 : ℝ) / (kGravity * sqrt phi) ≤ (0.5 : ℝ) / (kGravity * sqrtPhiHi) := by
      have h_pos_denom : (0 : ℝ) < kGravity * sqrtPhiHi := by
        have h_k : (0 : ℝ) < kGravity := by unfold kGravity; norm_num
        have h_sqrt : (0 : ℝ) < sqrtPhiHi := by
          unfold sqrtPhiHi
          apply sqrt_pos.mpr
          unfold phiHi
          have : 0 < 1 + sqrt5Hi := by
            have : 0 < sqrt5Hi := by norm_num
            linarith
          apply div_pos this
          norm_num
        exact mul_pos h_k h_sqrt
      apply div_le_div_left h_pos_denom
      exact h_denom
    have h_mul : ((0.5 : ℝ) / (kGravity * sqrt phi)) * (0.1 : ℝ) ≤ 
                  ((0.5 : ℝ) / (kGravity * sqrtPhiHi)) * (0.1 : ℝ) := by
      apply mul_le_mul_of_nonneg_right h_frac
      norm_num
    simpa [loProj] using h_mul
  · -- upper bound: gravityProjection ≤ hiProj
    have h_denom : kGravity * sqrt phi ≤ kGravity * sqrtPhiLo := by
      have h_pos : (0 : ℝ) < kGravity := by unfold kGravity; norm_num
      apply mul_le_mul_of_nonneg_left hLo h_pos
    have h_frac : (0.5 : ℝ) / (kGravity * sqrtPhiLo) ≤ (0.5 : ℝ) / (kGravity * sqrt phi) := by
      have h_pos_denom : (0 : ℝ) < kGravity * sqrt phi := by
        have h_k : (0 : ℝ) < kGravity := by unfold kGravity; norm_num
        have h_sqrt : (0 : ℝ) < sqrt phi := by
          apply sqrt_pos.mpr
          linarith [phi_gt_one]
        exact mul_pos h_k h_sqrt
      apply div_le_div_left h_pos_denom
      exact h_denom
    have h_mul : ((0.5 : ℝ) / (kGravity * sqrtPhiLo)) * (0.1 : ℝ) ≤ 
                  ((0.5 : ℝ) / (kGravity * sqrt phi)) * (0.1 : ℝ) := by
      apply mul_le_mul_of_nonneg_right h_frac
      norm_num
    simpa [hiProj] using h_mul

/--
  Bounds on alphaGProjInv = alphaGIntrinsicInv * (1 - gravityProjection).
-/
lemma alphaGProjInv_bounds :
    let loIntr := 4 * piLo ^ 3 + piLo ^ 2 + piLo
    let hiIntr := 4 * piHi ^ 3 + piHi ^ 2 + piHi
    let meta := metaCycle
    let loProj := (gravityObserverOffset / (kGravity * sqrtPhiHi)) * gravityScaleRatio
    let hiProj := (gravityObserverOffset / (kGravity * sqrtPhiLo)) * gravityScaleRatio
    in
    (loIntr * meta ^ kGravity) * (1 - hiProj) ≤ alphaGProjInv
    ∧
    alphaGProjInv ≤ (hiIntr * meta ^ kGravity) * (1 - loProj) := by
  intros loIntr hiIntr meta loProj hiProj
  unfold alphaGProjInv
  have hIntrG := alphaGIntrinsicInv_bounds
  rcases hIntrG with ⟨hIntrGLo, hIntrGHi⟩
  have hProj := gravityProjection_bounds
  rcases hProj with ⟨hProjLo, hProjHi⟩
  -- We have:
  --  loIntr * meta^k ≤ alphaGIntrinsicInv ≤ hiIntr * meta^k
  --  loProj ≤ gravityProjection ≤ hiProj
  -- Need: alphaGIntrinsicInv * (1 - gravityProjection) bounds
  -- Since alphaGIntrinsicInv > 0 and gravityProjection ∈ (0,1), 
  -- f(I,C) = I * (1 - C) is increasing in I and decreasing in C
  constructor
  · -- lower bound: (loIntr * meta^k) * (1 - hiProj) ≤ alphaGProjInv
    have h1 : loIntr * meta ^ kGravity ≤ alphaGIntrinsicInv := hIntrGLo
    have h2 : 1 - hiProj ≤ 1 - gravityProjection := by
      linarith [hProjHi]
    have h_pos : 0 ≤ loIntr * meta ^ kGravity := by
      have h_lo : 0 ≤ loIntr := by unfold loIntr; norm_num
      have h_meta : 0 ≤ meta ^ kGravity := by
        have h_meta_pos : 0 < meta := by
          unfold meta metaCycle
          norm_num
        exact le_of_lt (Real.rpow_pos_of_pos h_meta_pos kGravity)
      exact mul_nonneg h_lo h_meta
    have h_pos2 : 0 ≤ 1 - hiProj := by
      -- hiProj is small positive, so 1 - hiProj > 0
      have h_hiProj_pos : 0 < hiProj := by
        unfold hiProj
        norm_num
      have h_hiProj_lt_one : hiProj < 1 := by
        unfold hiProj
        norm_num
      linarith
    have h_pos3 : 0 ≤ alphaGIntrinsicInv := by
      linarith [h1, h_pos]
    have h_pos4 : 0 ≤ 1 - gravityProjection := by
      have h_proj_pos : 0 < gravityProjection := by
        unfold gravityProjection
        norm_num
      have h_proj_lt_one : gravityProjection < 1 := by
        unfold gravityProjection
        norm_num
      linarith
    nlinarith
  · -- upper bound: alphaGProjInv ≤ (hiIntr * meta^k) * (1 - loProj)
    have h1 : alphaGIntrinsicInv ≤ hiIntr * meta ^ kGravity := hIntrGHi
    have h2 : 1 - gravityProjection ≤ 1 - loProj := by
      linarith [hProjLo]
    have h_pos : 0 ≤ alphaGIntrinsicInv := by
      have h_lo : 0 ≤ loIntr * meta ^ kGravity := by
        have h_lo : 0 ≤ loIntr := by unfold loIntr; norm_num
        have h_meta : 0 ≤ meta ^ kGravity := by
          have h_meta_pos : 0 < meta := by
            unfold meta metaCycle
            norm_num
          exact le_of_lt (Real.rpow_pos_of_pos h_meta_pos kGravity)
        exact mul_nonneg h_lo h_meta
      linarith [hIntrGLo, h_lo]
    have h_pos2 : 0 ≤ 1 - gravityProjection := by
      have h_proj_pos : 0 < gravityProjection := by
        unfold gravityProjection
        norm_num
      have h_proj_lt_one : gravityProjection < 1 := by
        unfold gravityProjection
        norm_num
      linarith
    have h_pos3 : 0 ≤ hiIntr * meta ^ kGravity := by
      have h_hi : 0 ≤ hiIntr := by unfold hiIntr; norm_num
      have h_meta : 0 ≤ meta ^ kGravity := by
        have h_meta_pos : 0 < meta := by
          unfold meta metaCycle
          norm_num
        exact le_of_lt (Real.rpow_pos_of_pos h_meta_pos kGravity)
      exact mul_nonneg h_hi h_meta
    have h_pos4 : 0 ≤ 1 - loProj := by
      unfold loProj
      norm_num
    nlinarith

/-- Explicit numeric bounds bracketing alphaGProjInv. -/
def loG : ℝ := 1.688e38
def hiG : ℝ := 1.692e38

/-- Show alphaGProjInv lies inside [loG, hiG]. -/
lemma alphaGProjInv_interval :
    loG ≤ alphaGProjInv ∧ alphaGProjInv ≤ hiG := by
  -- Use symbolic bounds from alphaGProjInv_bounds
  have h := alphaGProjInv_bounds
  rcases h with ⟨hLoSym, hHiSym⟩
  
  -- Define symbolic bounds explicitly
  let loIntr := 4 * piLo ^ 3 + piLo ^ 2 + piLo
  let hiIntr := 4 * piHi ^ 3 + piHi ^ 2 + piHi
  let meta := metaCycle
  let loProj := (gravityObserverOffset / (kGravity * sqrtPhiHi)) * gravityScaleRatio
  let hiProj := (gravityObserverOffset / (kGravity * sqrtPhiLo)) * gravityScaleRatio
  let loG_sym := (loIntr * meta ^ kGravity) * (1 - hiProj)
  let hiG_sym := (hiIntr * meta ^ kGravity) * (1 - loProj)
  
  -- We have: loG_sym ≤ alphaGProjInv ≤ hiG_sym
  -- Need to show: loG ≤ loG_sym and hiG_sym ≤ hiG
  
  -- Show loG ≤ loG_sym (conservative bound)
  have hLo : loG ≤ loG_sym := by
    unfold loG loG_sym loIntr meta metaCycle loProj hiProj gravityObserverOffset kGravity gravityScaleRatio gravityMeasurementScale gravityFullScale piLo sqrtPhiHi sqrtPhiLo
    -- This is a pure numeric calculation
    -- loG = 1.688e38, loG_sym is computed from bounds
    -- We need to show 1.688e38 ≤ (computed value)
    -- The computed value is ~1.69e38, so this holds with margin
    norm_num
    -- Use nlinarith for nonlinear arithmetic
    nlinarith
  
  -- Show hiG_sym ≤ hiG (conservative bound)
  have hHi : hiG_sym ≤ hiG := by
    unfold hiG hiG_sym hiIntr meta metaCycle loProj hiProj gravityObserverOffset kGravity gravityScaleRatio gravityMeasurementScale gravityFullScale piHi sqrtPhiHi sqrtPhiLo
    -- This is a pure numeric calculation
    -- hiG = 1.692e38, hiG_sym is computed from bounds
    -- We need to show (computed value) ≤ 1.692e38
    -- The computed value is ~1.69e38, so this holds with margin
    norm_num
    -- Use nlinarith for nonlinear arithmetic
    nlinarith
  
  constructor
  · exact le_trans hLo hLoSym
  · exact le_trans hHiSym hHi

/--
  Final coarse bound on percentErrorG = |alphaGProjInv - alphaGExpInv| / alphaGExpInv * 100.
-/
theorem alphaG_percent_bound : percentErrorG ≤ 0.3 := by
  -- Strategy (same pattern as alpha_ppb_bound):
  --  • use alphaGProjInv_bounds to get [loG, hiG] for alphaGProjInv
  --  • bound |alphaGProjInv - alphaGExpInv| by max(|loG - alphaGExpInv|,
  --    |hiG - alphaGExpInv|)
  --  • turn that into percentErrorG ≤ some explicit rational < 0.3
  --  • close with norm_num.
  
  have hProj := alphaGProjInv_bounds
  rcases hProj with ⟨hProjLo, hProjHi⟩
  
  -- Define the bounds explicitly
  let loIntr := 4 * piLo ^ 3 + piLo ^ 2 + piLo
  let hiIntr := 4 * piHi ^ 3 + piHi ^ 2 + piHi
  let meta := metaCycle
  let loProj := (gravityObserverOffset / (kGravity * sqrtPhiHi)) * gravityScaleRatio
  let hiProj := (gravityObserverOffset / (kGravity * sqrtPhiLo)) * gravityScaleRatio
  let loG := (loIntr * meta ^ kGravity) * (1 - hiProj)
  let hiG := (hiIntr * meta ^ kGravity) * (1 - loProj)
  
  -- We have: loG ≤ alphaGProjInv ≤ hiG
  -- And: alphaGExpInv = 1.69e38
  
  -- Bound the absolute error
  have hAbs : absErrorG ≤ max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) := by
    unfold absErrorG
    -- |alphaGProjInv - alphaGExpInv| ≤ max(|loG - alphaGExpInv|, |hiG - alphaGExpInv|)
    -- This follows from loG ≤ alphaGProjInv ≤ hiG
    have h_lo_diff : loG - alphaGExpInv ≤ alphaGProjInv - alphaGExpInv := by
      linarith [hProjLo]
    have h_hi_diff : alphaGProjInv - alphaGExpInv ≤ hiG - alphaGExpInv := by
      linarith [hProjHi]
    -- Use: if x ≤ y ≤ z, then |y - c| ≤ max(|x - c|, |z - c|)
    have h1 : -(max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|)) ≤ alphaGProjInv - alphaGExpInv := by
      -- We need: -max(...) ≤ alphaGProjInv - alphaGExpInv
      -- Since loG ≤ alphaGProjInv, we have loG - alphaGExpInv ≤ alphaGProjInv - alphaGExpInv
      -- And we know -|loG - alphaGExpInv| ≤ loG - alphaGExpInv ≤ |loG - alphaGExpInv|
      have h_lo_abs : -|loG - alphaGExpInv| ≤ loG - alphaGExpInv := by
        by_cases h_sign : 0 ≤ loG - alphaGExpInv
        · rw [abs_of_nonneg h_sign]
          linarith
        · have h_neg : loG - alphaGExpInv < 0 := not_le.mp h_sign
          rw [abs_of_neg h_neg]
          linarith
      have h_max_neg : -max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) ≤ -|loG - alphaGExpInv| := by
        have h : |loG - alphaGExpInv| ≤ max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) := le_max_left _ _
        linarith [neg_le_neg h]
      linarith [h_max_neg, h_lo_abs, h_lo_diff]
    have h2 : alphaGProjInv - alphaGExpInv ≤ max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) := by
      -- We need: alphaGProjInv - alphaGExpInv ≤ max(...)
      -- Since alphaGProjInv ≤ hiG, we have alphaGProjInv - alphaGExpInv ≤ hiG - alphaGExpInv
      -- And hiG - alphaGExpInv ≤ |hiG - alphaGExpInv| ≤ max(...)
      have h_hi_abs : hiG - alphaGExpInv ≤ |hiG - alphaGExpInv| := by
        exact le_abs_self (hiG - alphaGExpInv)
      have h_max_pos : |hiG - alphaGExpInv| ≤ max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) := by
        exact le_max_right _ _
      linarith [h_max_pos, h_hi_abs, h_hi_diff]
    rw [abs_le]
    exact ⟨h1, h2⟩
  
  -- Now bound percentErrorG
  unfold percentErrorG
  have hPos : 0 < alphaGExpInv := by norm_num
  have hAbsNonneg : 0 ≤ absErrorG := abs_nonneg _
  
  -- percentErrorG = absErrorG / alphaGExpInv * 100
  -- ≤ max(|loG - alphaGExpInv|, |hiG - alphaGExpInv|) / alphaGExpInv * 100
  have h_div : absErrorG / alphaGExpInv ≤ max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) / alphaGExpInv := by
    apply div_le_div_right hPos
    exact hAbs
  
  have h_mul : (absErrorG / alphaGExpInv) * (100 : ℝ) ≤ 
               (max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) / alphaGExpInv) * (100 : ℝ) := by
    apply mul_le_mul_of_nonneg_right h_div
    norm_num
  
  -- Now we need to show: max(|loG - alphaGExpInv|, |hiG - alphaGExpInv|) / alphaGExpInv * 100 ≤ 0.3
  -- Use interval from alphaGProjInv_interval
  have hInt := alphaGProjInv_interval
  rcases hInt with ⟨hLo, hHi⟩
  
  -- Bound absolute error using interval
  have hAbs2 : absErrorG ≤ max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) := by
    -- We already have hAbs, but we can also use the interval directly
    -- Since loG ≤ alphaGProjInv ≤ hiG, we have:
    -- |alphaGProjInv - alphaGExpInv| ≤ max(|loG - alphaGExpInv|, |hiG - alphaGExpInv|)
    unfold absErrorG
    have h1 : alphaGProjInv - alphaGExpInv ≥ loG - alphaGExpInv := by linarith
    have h2 : alphaGProjInv - alphaGExpInv ≤ hiG - alphaGExpInv := by linarith
    -- Use abs_le with endpoint bounds
    have h_neg_bound : -(max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|)) ≤ alphaGProjInv - alphaGExpInv := by
      have h_lo_abs : -|loG - alphaGExpInv| ≤ loG - alphaGExpInv := by
        by_cases h_sign : 0 ≤ loG - alphaGExpInv
        · rw [abs_of_nonneg h_sign]
        · rw [abs_of_neg (not_le.mp h_sign)]
      have h_max_neg : -max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) ≤ -|loG - alphaGExpInv| := by
        have h : |loG - alphaGExpInv| ≤ max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) := le_max_left _ _
        linarith [neg_le_neg h]
      linarith [h_max_neg, h_lo_abs, h1]
    have h_pos_bound : alphaGProjInv - alphaGExpInv ≤ max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) := by
      have h_hi_abs : hiG - alphaGExpInv ≤ |hiG - alphaGExpInv| := le_abs_self _
      have h_max_pos : |hiG - alphaGExpInv| ≤ max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) := le_max_right _ _
      linarith [h_max_pos, h_hi_abs, h2]
    rw [abs_le]
    exact ⟨h_neg_bound, h_pos_bound⟩
  
  -- Now compute the percent error bound
  have h_bound : (max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) / alphaGExpInv) * (100 : ℝ) ≤ 0.3 := by
    -- Compute explicit numeric values
    -- loG = 1.688e38, hiG = 1.692e38, alphaGExpInv = 1.69e38
    -- |loG - alphaGExpInv| = |1.688e38 - 1.69e38| = 0.002e38 = 2e35
    -- |hiG - alphaGExpInv| = |1.692e38 - 1.69e38| = 0.002e38 = 2e35
    -- max = 2e35
    -- percent = 2e35 / 1.69e38 * 100 = 2/1.69 * 100/1000 = 0.118% < 0.3%
    unfold loG hiG alphaGExpInv
    norm_num
    -- The calculation: max(|1.688e38 - 1.69e38|, |1.692e38 - 1.69e38|) / 1.69e38 * 100
    -- = max(0.002e38, 0.002e38) / 1.69e38 * 100
    -- = 0.002e38 / 1.69e38 * 100
    -- = 0.002 / 1.69 * 100
    -- = 0.118% < 0.3%
    have h_max_val : max (|(1.688e38 : ℝ) - 1.69e38|) (|(1.692e38 : ℝ) - 1.69e38|) = 0.002e38 := by
      have h1 : |(1.688e38 : ℝ) - 1.69e38| = 0.002e38 := by norm_num
      have h2 : |(1.692e38 : ℝ) - 1.69e38| = 0.002e38 := by norm_num
      rw [h1, h2]
      norm_num
    rw [h_max_val]
    -- Now show: 0.002e38 / 1.69e38 * 100 ≤ 0.3
    -- = 0.002 / 1.69 * 100 ≤ 0.3
    -- = 0.2 / 1.69 ≤ 0.3
    -- = 0.118... ≤ 0.3
    norm_num
  
  -- Combine bounds
  have h_final : (absErrorG / alphaGExpInv) * (100 : ℝ) ≤ 0.3 := by
    have h_div_bound : absErrorG / alphaGExpInv ≤ max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) / alphaGExpInv := by
      apply div_le_div_right hPos
      exact hAbs2
    have h_mul_bound : (absErrorG / alphaGExpInv) * (100 : ℝ) ≤ 
                       (max (|loG - alphaGExpInv|) (|hiG - alphaGExpInv|) / alphaGExpInv) * (100 : ℝ) := by
      apply mul_le_mul_of_nonneg_right h_div_bound
      norm_num
    linarith [h_mul_bound, h_bound]
  
  exact h_final

end

