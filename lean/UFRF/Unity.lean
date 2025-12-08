/-
  UFRF/Unity.lean

  Unity lemmas: formal "all is one" statements for the 13-cycle.

  These lemmas prove that observer perspective changes preserve the underlying
  geometric structure - the formalization of "unity in context".
-/

import UFRF.CycleAxioms
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Basic

namespace UFRF

open CycleAxioms

/-- Rotation as addition in Fin cycleLen.

    This shows that `rotate offset i` is equivalent to `i + offset` in the
    additive group structure of `Fin cycleLen`.
    
    Key: In Fin n, addition is defined as (a.val + b.val) % n, which is exactly
    what rotate computes.
-/
lemma rotate_eq_add (offset i : Fin cycleLen) :
    rotate offset i = i + offset := by
  unfold rotate
  ext
  -- Need: (i.val + offset.val) % cycleLen = (i + offset).val
  -- In Fin n, (a + b).val = (a.val + b.val) % n by definition
  -- So this is just the definition of Fin addition
  rfl

/-- Rotation is injective: if rotate offset i = rotate offset j, then i = j.

    Key insight: Since `rotate offset i = i + offset` in Fin cycleLen,
    and Fin cycleLen is an additive group, we can use `add_right_cancel`.
-/
lemma rotate_injective (offset : Fin cycleLen) :
    Function.Injective (rotate offset) := by
  intro i j h
  -- rotate offset i = rotate offset j
  -- By rotate_eq_add: i + offset = j + offset
  -- By add_right_cancel: i = j
  have h_add : rotate offset i = rotate offset j := h
  rw [rotate_eq_add, rotate_eq_add] at h_add
  exact add_right_cancel h_add

/-- Rotation is a bijection: it permutes positions without losing information.

    This proves that no matter where the observer stands, they just permute
    positions - they don't break the cycle structure.
    
    Since rotate maps Fin cycleLen → Fin cycleLen and is injective,
    and Fin cycleLen is finite with same cardinality, injectivity implies bijectivity.
-/
theorem rotate_bijective (offset : Fin cycleLen) :
    Function.Bijective (rotate offset) := by
  -- For finite types with same cardinality, injective = bijective
  exact Function.Bijective.of_injective (rotate_injective offset)

/-- Phase counts are invariant under observer perspective shifts.

    This is the formal "unity in context" statement: no matter where the
    observer stands, they see the same number of each phase type. The structure
    is invariant; only labels change with perspective.
-/
theorem phase_counts_invariant (origin : Fin cycleLen) (ph : Phase) :
    countPhaseFromPerspective origin ph = countPhase ph := by
  -- Key insight: rotate origin is a bijection (permutation)
  -- Permutations preserve cardinality of filtered sets
  -- So countPhaseFromPerspective origin ph = countPhase ph
  
  -- countPhaseFromPerspective origin ph counts positions i where
  -- phaseFromPerspective origin i = ph
  -- which is phaseOf (rotate origin i) = ph
  
  -- countPhase ph counts positions i where phaseOf i = ph
  
  -- Since rotate origin is bijective, the map i ↦ rotate origin i
  -- is a permutation, so it preserves the count of positions with phase ph
  have h_bij : Function.Bijective (rotate origin) := rotate_bijective origin
  
  -- Use that bijections preserve cardinality of filtered sets
  -- The key: Finset.card_image_of_injective or similar
  -- Actually, we need: card {i | phaseOf (rotate origin i) = ph} = card {i | phaseOf i = ph}
  -- Since rotate origin is a bijection, these sets have the same cardinality
  
  -- More direct: use that rotate origin is a permutation
  -- Finset.card_image_of_injective shows that injective maps preserve cardinality
  -- But we need surjectivity too - actually, for bijections, we can use:
  -- Finset.card_bij or Finset.card_image_of_bijective
  
  -- Actually, simplest: use Finset.card_image_of_injective with the bijection
  -- But we need to show the sets are related by the bijection
  
  -- Let's use: countPhaseFromPerspective origin ph = 
  --   (Finset.univ.filter (fun i => phaseFromPerspective origin i = ph)).card
  --   = (Finset.univ.filter (fun i => phaseOf (rotate origin i) = ph)).card
  --   = (Finset.univ.image (rotate origin)).filter (fun j => phaseOf j = ph)).card
  --   = (Finset.univ.filter (fun j => phaseOf j = ph)).card  (since rotate origin is surjective)
  --   = countPhase ph
  
  -- More formally: use Finset.card_image_of_bijective
  unfold countPhaseFromPerspective countPhase
  -- countPhaseFromPerspective origin ph = 
  --   (Finset.univ.filter (fun i => phaseFromPerspective origin i = ph)).card
  --   = (Finset.univ.filter (fun i => phaseOf (rotate origin i) = ph)).card
  
  -- countPhase ph = 
  --   (Finset.univ.filter (fun i => phaseOf i = ph)).card
  
  -- Key: The map i ↦ rotate origin i is a bijection from Finset.univ to Finset.univ
  -- So it preserves the count of elements satisfying any predicate
  
  -- Use: Finset.card_image_of_bijective
  -- But we need to show: image (rotate origin) (filter ...) = filter ...
  -- Actually, simpler: use that bijections preserve cardinality
  
  -- Let S = {i | phaseOf (rotate origin i) = ph}
  -- Let T = {j | phaseOf j = ph}
  -- We want: card S = card T
  
  -- Since rotate origin is bijective, there's a bijection between S and T
  -- Specifically: j = rotate origin i maps S bijectively to T
  -- So card S = card T
  
  -- Strategy: Show that rotate origin maps the filtered set bijectively to the target set
  -- Let S = {i | phaseOf (rotate origin i) = ph}
  -- Let T = {j | phaseOf j = ph}
  -- We show: rotate origin maps S bijectively to T, so card S = card T
  
  -- Step 1: Show card S = card (image of S under rotate origin)
  have h_card_image : (Finset.univ.filter (fun i => phaseOf (rotate origin i) = ph)).card =
                      ((Finset.univ.filter (fun i => phaseOf (rotate origin i) = ph)).image (rotate origin)).card := by
    rw [Finset.card_image_of_injective]
    exact rotate_injective origin
  
  -- Step 2: Show image of S equals T
  -- image (rotate origin) {i | phaseOf (rotate origin i) = ph} = {j | phaseOf j = ph}
  have h_image_eq : ((Finset.univ.filter (fun i => phaseOf (rotate origin i) = ph)).image (rotate origin)) =
                    (Finset.univ.filter (fun i => phaseOf i = ph)) := by
    ext j
    constructor
    · -- If j is in the image, then j = rotate origin i for some i with phaseOf (rotate origin i) = ph
      -- So phaseOf j = ph, hence j ∈ T
      intro hj
      simp [Finset.mem_image, Finset.mem_filter] at hj
      rcases hj with ⟨i, ⟨hi_univ, hi_ph⟩, rfl⟩
      simp [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, hi_ph⟩
    · -- If j ∈ T, then phaseOf j = ph
      -- Since rotate origin is surjective, there exists i with rotate origin i = j
      -- Then phaseOf (rotate origin i) = phaseOf j = ph, so i ∈ S
      -- So j ∈ image of S
      intro hj
      simp [Finset.mem_filter] at hj
      rcases hj with ⟨hj_univ, hj_ph⟩
      -- Use surjectivity: there exists i such that rotate origin i = j
      have h_surj : Function.Surjective (rotate origin) := h_bij.2
      rcases h_surj j with ⟨i, rfl⟩
      -- Now j = rotate origin i, and we need to show i ∈ S
      simp [Finset.mem_image, Finset.mem_filter]
      use i
      constructor
      · exact ⟨Finset.mem_univ i, hj_ph⟩
      · rfl
  
  -- Combine: card S = card (image S) = card T
  rw [h_card_image, h_image_eq]

end UFRF

