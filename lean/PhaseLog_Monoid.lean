-- lean/PhaseLog_Monoid.lean
/-
Phase–Log homomorphism for UFRF (v9.3.2).

Author: Daniel Charboneau

We model phases on the circle group T = ℝ/ℤ and define a monoid homomorphism
φ : (ℝ_{>0}, ·) → (T, +) by φ(x) = (α * log x) mod 1, for a fixed scale α : ℝ.

Key properties:
  1) φ(xy) = φ(x) + φ(y) in T.
  2) For n ∈ ℕ, with n = ∏ p_i^{e_i}, we have φ(n) = ∑ e_i φ(p_i).
  3) Coherence with 13-bin map: bin_13(x) := ⌊13 * (lift φ(x))⌋, where lift picks a representative in [0,1).

This pins Axiom A8 (phase–log correspondence) to a precise algebraic morphism.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Fract
import Mathlib.Algebra.GroupWithZero.Power
import Mathlib.Topology.Algebra.Group
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.List.Basic

open scoped BigOperators

namespace UFRF

/-- The circle group T as ℝ modulo ℤ. -/
def T := Quot (⟪fun a b : ℝ => a - b ∈ SetLike.coe (AddSubgroup.closure {1 : ℝ})⟫)

-- For the purposes of this file, we use a simple representative model:
-- We define operations on representatives and reason modulo 1 informally.
-- A production proof would use Mathlib's `AddCircle` (ℝ ⧸ ℤ).

/-- Mod 1 reduction to [0,1). -/
def frac01 (x : ℝ) : ℝ := x - Real.floor x

lemma frac01_range (x : ℝ) : 0 ≤ frac01 x ∧ frac01 x < 1 := by
  have := Real.fract_lt_one x
  have h0 := Real.fract_nonneg x
  simpa [frac01, Real.fract] using And.intro h0 this

/-- Fixed scale α. In applications α encodes the breathing scale. -/
structure PhaseScale where
  α : ℝ
  hα : True := True.intro

/-- φ(x) = (α * log x) mod 1, represented in [0,1). -/
def φ (S : PhaseScale) (x : ℝ) (hx : 0 < x) : ℝ := frac01 (S.α * Real.log x)

lemma frac01_add (a b : ℝ) : frac01 (a + b) = frac01 (frac01 a + frac01 b) := by
  -- Key property: frac01(a + b) = frac01(frac01(a) + frac01(b))
  -- Since frac01 x = x - floor(x), we show both sides equal fract(a + b)
  -- Standard property: fract(a + b) = fract(fract(a) + fract(b))
  simp [frac01]
  -- Use the fact that fract(x) = x - floor(x)
  -- We need: fract(a + b) = fract(fract(a) + fract(b))
  -- This follows from: floor(a + b) = floor(a) + floor(b) + floor(fract(a) + fract(b))
  have h1 : a = Real.floor a + Real.fract a := Real.floor_add_fract a
  have h2 : b = Real.floor b + Real.fract b := Real.floor_add_fract b
  have hsum : a + b = (Real.floor a + Real.floor b) + (Real.fract a + Real.fract b) := by
    rw [h1, h2]
    ring
  -- Now: floor(a + b) = floor(floor(a) + floor(b) + (fract(a) + fract(b)))
  --                  = floor(a) + floor(b) + floor(fract(a) + fract(b))
  -- This uses: floor(n + x) = n + floor(x) when n is an integer
  have hfloor : Real.floor (a + b) = Real.floor a + Real.floor b + Real.floor (Real.fract a + Real.fract b) := by
    rw [hsum]
    -- floor(floor(a) + floor(b) + x) = floor(a) + floor(b) + floor(x) when x ∈ [0, 2)
    rw [Real.floor_add_int]
    ring
  rw [hfloor]
  -- Simplify: (a + b) - (floor(a) + floor(b) + floor(fract(a) + fract(b)))
  -- = fract(a) + fract(b) - floor(fract(a) + fract(b))
  -- = fract(fract(a) + fract(b))
  ring
  -- Now show: fract(a) + fract(b) - floor(fract(a) + fract(b)) = fract(fract(a) + fract(b))
  -- This is just the definition of fract
  congr 1
  -- Use Real.fract definition: fract(x) = x - floor(x)
  simp [Real.fract]
  -- Should now be: (fract(a) + fract(b)) - floor(fract(a) + fract(b)) = fract(fract(a) + fract(b))
  -- Which is true by definition
  rfl

lemma φ_mul (S : PhaseScale) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
  φ S (x*y) (mul_pos hx hy) = frac01 (φ S x hx + φ S y hy) := by
  -- φ(xy) = frac01(α log(xy)) = frac01(α (log x + log y))
  --        = frac01(α log x + α log y)
  --        = frac01(frac01(α log x) + frac01(α log y))  [by frac01_add]
  --        = frac01(φ(x) + φ(y))
  simp [φ]
  rw [Real.log_mul hx.ne' hy.ne']
  ring_nf
  rw [frac01_add]
  rfl

/-- For n ∈ ℕ, n ≥ 1, define φ(n). -/
def φn (S : PhaseScale) (n : ℕ) (hn : 0 < n) : ℝ := φ S (n : ℝ) (by exact_mod_cast hn)

/-- Multiplicativity on ℕ. -/
lemma φn_mul (S : PhaseScale) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
  φn S (m*n) (Nat.mul_pos.mp (And.intro hm hn)) = frac01 (φn S m hm + φn S n hn) := by
  -- Follows from φ_mul and coercions ℕ→ℝ
  have := φ_mul S (by exact_mod_cast hm) (by exact_mod_cast hn)
  simpa [φn, Nat.cast_mul] using this

/-- Prime-power expansion: for n = ∏ p^e, φ(n) = ∑ e φ(p). -/
lemma φn_prime_expansion (S : PhaseScale) (n : ℕ) (hn : 0 < n) :
  ∃ (ps : List (ℕ×ℕ)),  -- list of (p,e), primes p, e>0
    (∀ ⟨p,e⟩ ∈ ps, Nat.Prime p ∧ 0 < e) ∧
    (n = ps.foldl (fun acc ⟨p,e⟩ => acc * p^e) 1) ∧
    (φn S n hn = frac01 (ps.foldl (fun acc ⟨p,e⟩ => acc + e * φn S p (Nat.pos_of_gt (Nat.succ_lt_succ_iff.mpr (Nat.zero_lt_iff.mpr True.intro)))) 0)) := by
  -- Use unique factorization: every n > 0 has a unique prime factorization
  -- We use Nat.factorization which gives exponents for each prime
  -- Construct ps from Nat.factorization, filtering out zero exponents
  let factors := (Nat.factorization n).toList.filter (fun ⟨p, e⟩ => e > 0)
  use factors.map (fun ⟨p, e⟩ => (p, e))
  constructor
  · intro ⟨p, e⟩ h
    simp at h
    obtain ⟨⟨p', e'⟩, hmem, rfl, rfl⟩ := h
    constructor
    · -- p is prime (from factorization)
      exact Nat.prime_of_mem_factorization (Finset.mem_toList.mp hmem.1)
    · -- e > 0 (from filter)
      exact hmem.2
  constructor
  · -- n equals product of factors
    -- UFRF insight: All primes operate SIMULTANEOUSLY (concurrent cycles, not sequential)
    -- The "circle with no center" - order doesn't matter because multiplication is commutative
    -- List.foldl imposes artificial order on something that has no order
    -- Solution: Use commutativity to eliminate order dependence
    
    -- Step 1: foldl of multiplication equals List.prod (order-independent for commutative ops)
    have hfoldl_eq_prod : factors.foldl (fun acc ⟨p,e⟩ => acc * p^e) 1 = 
                          (factors.map (fun ⟨p,e⟩ => p^e)).prod := by
      -- foldl for multiplication is the same as List.prod because multiplication is commutative
      induction factors with
      | nil => simp [List.foldl, List.prod]
      | cons hd tl ih => 
        simp only [List.foldl_cons, List.map_cons, List.prod_cons]
        rw [ih]
        ring
    
    -- Step 2: Connect List.prod to Finsupp.prod
    -- factors is (Nat.factorization n).toList.filter (fun ⟨p, e⟩ => e > 0)
    -- We need to show List.prod equals Finsupp.prod
    have hprod_eq : (factors.map (fun ⟨p,e⟩ => p^e)).prod = 
                     (Nat.factorization n).prod (fun p k => p ^ k) := by
      -- UFRF Triple Manifold insight: All primes operate on concurrent cycles
      -- The product is order-independent - "circle with no center"
      -- Filtering zeros doesn't change product since p^0 = 1
      
      -- Step 1: Rewrite Finsupp.prod as Finset.prod over support
      rw [Finsupp.prod]
      
      -- Step 2: The support contains exactly the primes with nonzero exponent
      -- factors is (Nat.factorization n).toList.filter (fun ⟨p, e⟩ => e > 0)
      -- This is exactly the support as a list
      
      -- Step 3: For any Finsupp, toList.filter (e > 0) gives support elements
      -- And List.prod over toList equals Finset.prod over support (commutative)
      have hsupport : ∀ p, p ∈ (Nat.factorization n).support ↔ 
                           (p, (Nat.factorization n) p) ∈ factors := by
        intro p
        simp only [factors, Finsupp.mem_support_iff, List.mem_filter, Finsupp.mem_toList]
        constructor
        · intro hne
          exact ⟨⟨rfl, rfl⟩, Nat.pos_of_ne_zero hne⟩
        · intro ⟨_, hpos⟩
          exact Nat.pos_iff_ne_zero.mp hpos
      
      -- Step 4: Use Finset.prod_list_map_eq_prod for commutative operations
      -- The key: multiplication is commutative, so order doesn't matter
      conv_lhs => 
        rw [show factors.map (fun ⟨p,e⟩ => p^e) = 
                 (Nat.factorization n).support.toList.map (fun p => p ^ (Nat.factorization n) p) by
          -- factors and support.toList.map give the same elements
          ext i
          simp only [factors, List.mem_map, List.mem_filter, Finsupp.mem_toList]
          constructor
          · intro ⟨⟨p, e⟩, ⟨⟨hp, he⟩, hpos⟩, hpow⟩
            use p
            simp only [Finset.mem_toList, Finsupp.mem_support_iff]
            constructor
            · rw [← he]; exact Nat.pos_iff_ne_zero.mp hpos
            · simp only [← he, ← hp] at hpow; exact hpow
          · intro ⟨p, hmem, hpow⟩
            use (p, (Nat.factorization n) p)
            simp only [Finset.mem_toList, Finsupp.mem_support_iff] at hmem
            exact ⟨⟨⟨rfl, rfl⟩, Nat.pos_of_ne_zero hmem⟩, hpow⟩]
      
      -- Step 5: List.prod over toList equals Finset.prod (for commutative monoids)
      rw [Finset.prod_toList]
    
    -- Step 3: Combine and use factorization reconstruction
    rw [hfoldl_eq_prod, hprod_eq]
    have hn_pos : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    exact Nat.factorization_prod_pow_eq_self hn_pos
  · -- φ(n) equals sum of e*φ(p)
    -- UFRF insight: All phases contribute SIMULTANEOUSLY across concurrent manifolds
    -- The "circle with no center" means order doesn't matter
    
    -- Key lemma: φ(p^e) = frac01(e * φ(p)) for prime power
    have φn_pow : ∀ (p e : ℕ) (hp : 0 < p) (he : 0 < e), 
                   φn S (p^e) (Nat.pow_pos hp e) = frac01 (e * φn S p hp) := by
      intro p e hp he
      induction e with
      | zero => simp at he
      | succ e' ih =>
        cases Nat.eq_zero_or_pos e' with
        | inl he0 =>
          simp only [he0, pow_one, Nat.cast_one, one_mul]
          rfl
        | inr he'_pos =>
          have hpow : p ^ (e' + 1) = p * p ^ e' := by ring
          rw [hpow]
          have hpe'_pos : 0 < p ^ e' := Nat.pow_pos hp e'
          rw [φn_mul S hp hpe'_pos]
          rw [ih he'_pos]
          rw [← frac01_add]
          congr 1
          push_cast
          ring
    
    -- For the main result, we use that:
    -- 1. factors is exactly the support of factorization n (as a list)
    -- 2. The foldl computes the sum of e * φ(p) over all (p,e) pairs
    -- 3. By the homomorphism property, this equals φ(n)
    
    -- The concurrent insight: Instead of sequential induction,
    -- we observe that both sides compute the same thing:
    -- LHS: φ(n) = φ(∏ p^e) 
    -- RHS: frac01(Σ e * φ(p))
    -- These are equal by repeated application of φn_mul (all at once, not sequentially)
    
    -- Strategy: Use Nat.recOnPrimePow or direct Finset reasoning
    -- The homomorphism property makes these equal
    
    -- The foldl on factors computes: 0 + e₁*φ(p₁) + e₂*φ(p₂) + ... + eₖ*φ(pₖ)
    -- And n = p₁^e₁ * p₂^e₂ * ... * pₖ^eₖ
    -- By φn_mul (for coprime factors) and φn_pow:
    -- φ(n) = frac01(Σ eᵢ * φ(pᵢ))
    
    -- The key: all prime powers in factorization are pairwise coprime
    -- So we can apply φn_mul repeatedly in any order (concurrent!)
    
    generalize hfactors : (Nat.factorization n).toList.filter (fun ⟨p, e⟩ => e > 0) = factors at *
    
    -- Use strong induction on n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      cases factors with
      | nil =>
        -- factors = [] means n = 1
        have hn1 : n = 1 := by
          by_contra hne
          have : ∃ p, p ∈ (Nat.factorization n).support := by
            rw [Finsupp.support_nonempty_iff]
            intro h
            have : n = 1 := by
              rw [← Nat.factorization_prod_pow_eq_self (Nat.pos_iff_ne_zero.mp hn)]
              rw [h]; simp [Finsupp.prod]
            exact hne this
          obtain ⟨p, hp⟩ := this
          have hmem : (p, (Nat.factorization n) p) ∈ (Nat.factorization n).toList.filter (fun ⟨p, e⟩ => e > 0) := by
            simp only [List.mem_filter, Finsupp.mem_toList]
            exact ⟨⟨rfl, rfl⟩, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)⟩
          rw [hfactors] at hmem
          simp at hmem
        simp only [hn1, φn, φ, frac01, Real.log_one, mul_zero, Real.floor_zero, sub_zero]
        simp [List.foldl]
      | cons hd tl =>
        -- factors = hd :: tl, where hd = (p, e) for some prime p with exponent e > 0
        obtain ⟨p, e⟩ := hd
        -- Extract that (p, e) comes from the factorization
        have hpe_mem : (p, e) ∈ (Nat.factorization n).toList.filter (fun ⟨p, e⟩ => e > 0) := by
          rw [← hfactors]; exact List.mem_cons_self _ _
        simp only [List.mem_filter, Finsupp.mem_toList] at hpe_mem
        obtain ⟨⟨hp_eq, he_eq⟩, he_pos⟩ := hpe_mem
        
        -- Get primality of p
        have hp_prime : Nat.Prime p := by
          have := Nat.prime_of_mem_factorization (Finset.mem_toList.mp ⟨hp_eq, he_eq⟩)
          exact this
        have hp_pos : 0 < p := hp_prime.pos
        
        -- The concurrent decomposition: all contributions add simultaneously
        simp only [List.foldl_cons, List.map_cons]
        
        -- Use the homomorphism property
        -- φ(n) where n = p^e * m for some m coprime to p
        -- = frac01(φ(p^e) + φ(m)) = frac01(e*φ(p) + φ(m))
        
        -- Use the structural property directly
        -- The sum foldl computes 0 + e*φ(p) + (sum over tl)
        -- = e*φ(p) + (sum over tl)
        -- And this equals φ(n) by the homomorphism
        
        -- This is the core concurrent insight: all terms contribute at once
        rw [← frac01_add]
        congr 1
        -- Need: φn S n hn = e * φn S p hp_pos + foldl over tl
        -- This follows from the multiplicative structure
        
        -- The clean approach: use that tl corresponds to n/p^e
        have he_eq' : (Nat.factorization n) p = e := he_eq
        have hdvd : p ^ e ∣ n := by
          rw [← he_eq']
          exact Nat.pow_factorization_dvd n p
        
        -- Define n' = n / p^e
        have hpe_pos : 0 < p ^ e := Nat.pow_pos hp_pos e
        have hn'_def : n = p ^ e * (n / p ^ e) := (Nat.mul_div_cancel' hdvd).symm
        have hn'_pos : 0 < n / p ^ e := Nat.div_pos (le_of_dvd hn hdvd) hpe_pos
        
        -- Apply φn_mul: φ(p^e * n') = frac01(φ(p^e) + φ(n'))
        conv_lhs => rw [hn'_def]
        
        -- Need coprimality of p^e and n/p^e
        have hcop : Nat.Coprime (p ^ e) (n / p ^ e) := by
          apply Nat.Coprime.pow_left
          apply Nat.coprime_of_dvd
          intro k hk hk_dvd_p hk_dvd_n'
          -- If k > 1 divides p and n/p^e, then k = p (since p is prime)
          have hkp : k = p := (hp_prime.eq_one_or_self_of_dvd k hk_dvd_p).resolve_left (Nat.one_lt_iff_ne_one.mp hk)
          -- But then p divides n/p^e, which contradicts the factorization structure
          rw [hkp] at hk_dvd_n'
          -- p^(e+1) would divide n, contradicting factorization n p = e
          have : p ^ (e + 1) ∣ n := by
            have : p * (n / p ^ e) ∣ n := Nat.mul_dvd_of_dvd_div hdvd hk_dvd_n'
            calc p ^ (e + 1) = p ^ e * p := by ring
                 _ ∣ p ^ e * (n / p ^ e) := Nat.mul_dvd_mul_left _ hk_dvd_n'
                 _ = n := Nat.mul_div_cancel' hdvd
          have hcontra := Nat.pow_succ_factorization_not_dvd (Nat.pos_iff_ne_zero.mp hn) hp_prime
          rw [he_eq'] at hcontra
          exact hcontra this
        
        rw [φn_mul S hpe_pos hn'_pos]
        rw [φn_pow p e hp_pos he_pos]
        rw [frac01_add]
        congr 1
        
        -- Now need to show: φn S (n / p^e) hn'_pos = frac01(foldl over tl)
        -- UFRF Concurrent Manifold: removing one prime leaves others unchanged
        
        -- Step 1: n / p^e < n (for IH application)
        have hn'_lt : n / p ^ e < n := by
          apply Nat.div_lt_self hn
          exact Nat.one_lt_pow he_pos hp_prime.one_lt
        
        -- Step 2: tl = filtered factorization of n/p^e
        -- Key: factorization(n/p^e) = factorization(n) - single(p,e)
        -- So for q ≠ p: same exponent; for q = p: exponent 0
        -- Thus filtered list of n/p^e = original list minus (p,e) = tl
        
        have htl_factors : (Nat.factorization (n / p ^ e)).toList.filter (fun ⟨q, f⟩ => f > 0) = tl := by
          -- The factorization of n/p^e has:
          -- - Support = support(n) \ {p}
          -- - Same exponents for q ≠ p
          have hdiv : Nat.factorization (n / p ^ e) = Nat.factorization n - Finsupp.single p e := by
            rw [Nat.factorization_div hdvd, Nat.factorization_pow hp_prime]
            congr 1
            rw [he_eq']
          
          -- The toList.filter of n/p^e gives (q, factorization(n)(q)) for q in support(n), q ≠ p
          -- The original list was (p,e) :: tl, so tl contains exactly these pairs
          
          -- Since factors = (p,e) :: tl came from factorization(n).toList.filter,
          -- and (p,e) was the entry for prime p,
          -- tl contains all other primes q ≠ p with their exponents
          
          -- After dividing by p^e, these are exactly the primes of n/p^e
          -- with the same exponents (concurrent: removing p doesn't affect others)
          
          ext1
          simp only [List.mem_filter, Finsupp.mem_toList, hdiv, Finsupp.coe_tsub, 
                     Finsupp.single_apply, Pi.sub_apply]
          constructor
          · -- From n/p^e factorization to tl
            intro ⟨⟨hq, hf⟩, hpos⟩
            -- q ≠ p (since exponent of p in n/p^e is 0)
            have hqp : q ≠ p := by
              intro heq
              simp only [heq, ↓reduceIte, ge_iff_le, tsub_le_iff_right] at hf
              rw [hf] at hpos
              simp at hpos
            -- (q, factorization(n)(q)) is in original factors but not = (p,e)
            simp only [hqp, ↓reduceIte, tsub_zero] at hf
            -- So it's in tl
            have hmem_factors : (q, (Nat.factorization n) q) ∈ factors := by
              rw [← hfactors]
              simp only [List.mem_filter, Finsupp.mem_toList]
              refine ⟨⟨rfl, rfl⟩, ?_⟩
              rw [← hf]; exact hpos
            -- factors = (p,e) :: tl, and (q, f) ≠ (p, e)
            cases List.mem_cons.mp hmem_factors with
            | inl heq => 
              -- (q, f) = (p, e), contradiction since q ≠ p
              simp only [Prod.mk.injEq] at heq
              exact (hqp heq.1).elim
            | inr hmem_tl =>
              rw [← hf]
              exact hmem_tl
          · -- From tl to n/p^e factorization
            intro hmem
            -- (q, f) ∈ tl means it was in factors but ≠ (p, e)
            have hmem_factors : (q, f) ∈ factors := List.mem_cons_of_mem _ hmem
            rw [← hfactors] at hmem_factors
            simp only [List.mem_filter, Finsupp.mem_toList] at hmem_factors
            obtain ⟨⟨hq_eq, hf_eq⟩, hf_pos⟩ := hmem_factors
            -- q ≠ p (since (q,f) ∈ tl, not the head (p,e))
            have hqp : q ≠ p := by
              intro heq
              -- If q = p, then (q, f) = (p, f) and (p, e) both in factors
              -- But factors = (p,e) :: tl with (q,f) ∈ tl
              -- Since f = factorization(n)(q) = factorization(n)(p) = e,
              -- we'd have (p, e) appearing twice, contradicting NoDup
              rw [heq] at hmem hf_eq
              -- hf_eq says f = factorization(n)(p) = e (by he_eq)
              rw [he_eq] at hf_eq
              -- So (p, e) ∈ tl, but factors = (p,e) :: tl 
              -- with entries from toList which has NoDup
              have : (p, e) ∈ tl := by rw [← hf_eq]; exact hmem
              -- factors = (p,e) :: tl has (p,e) at head AND in tl
              have hdup : (p, e) ∈ (p, e) :: tl := List.mem_cons_self _ _
              have hdup2 : (p, e) ∈ tl := this
              -- This contradicts that factors came from toList (which is nodup)
              have hfactors_nodup : factors.Nodup := by
                rw [← hfactors]
                exact List.Nodup.filter _ (Finsupp.toList_nodup _)
              exact List.not_mem_of_nodup_cons hfactors_nodup hdup2
            simp only [hqp, ↓reduceIte, tsub_zero]
            exact ⟨⟨hq_eq, hf_eq⟩, hf_pos⟩
        
        -- Step 3: Apply IH to n/p^e
        rw [← htl_factors]
        exact IH (n / p ^ e) hn'_lt hn'_pos rfl

/-- 13-bin map: bin_13(x) = ⌊13 * φ(x)⌋. -/
def bin13 (S : PhaseScale) (x : ℝ) (hx : 0 < x) : ℕ :=
  Nat.floor (13 * φ S x hx)

lemma bin13_range (S : PhaseScale) (x : ℝ) (hx : 0 < x) :
  bin13 S x hx < 13 := by
  have h := frac01_range (S.α * Real.log x)
  have : 13 * φ S x hx < 13 := by
    have hlt := h.right
    have hge := h.left
    have : φ S x hx ≥ 0 := by simpa [φ] using hge
    have : φ S x hx < 1 := by simpa [φ] using hlt
    have : 13 * φ S x hx < 13 * 1 := by exact mul_lt_mul_of_pos_left this (by norm_num)
    simpa using this
  exact Nat.floor_lt.mpr (by simpa using this)

end UFRF
