-- lean/Concurrency_BoundedGap.lean
/-
Bounded-gap theorem for multi-scale concurrency.

Author: Daniel Charboneau

We model a finite family of cycles with periods pᵢ ≥ 1 and active residue sets Aᵢ ⊆ {0,…,pᵢ−1}.
Active(t) :↔ ∃i a∈Aᵢ, t ≡ a [MOD pᵢ]. Let L = lcmᵢ pᵢ.
We prove:
  1) Active is L-periodic.
  2) If there exists an active time, then in every window [t, t+L) there is an active s.
Equivalently, the longest inactive run is ≤ L−1.
This eliminates unbounded rest at the formal level.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Basic

open Nat

namespace UFRF

structure Cycle where
  p : Nat
  hp : 0 < p
  A : Finset Nat
  hA : ∀ a ∈ A, a < p

def Family := List Cycle

def lcmFamily : Family → Nat
| []      => 1
| c :: cs => lcm c.p (lcmFamily cs)

lemma lcmFamily_pos (F : Family) : 0 < lcmFamily F := by
  induction F with
  | nil => simpa
  | cons c cs ih =>
    have : 0 < lcm c.p (lcmFamily cs) := by
      have hc : 0 < c.p := c.hp
      have hL : 0 < lcmFamily cs := ih
      exact Nat.pos_of_ne_zero (by
        intro h; cases c.p with
        | zero => cases hc
        | succ _ =>
          cases lcmFamily cs with
          | zero => cases hL
          | succ _ => contradiction)
    simpa [lcmFamily] using this

def Active (F : Family) (t : Nat) : Prop :=
  ∃ c ∈ F, ∃ a ∈ c.A, (t % c.p) = a

lemma mem_cons {α} {x : α} {L : List α} : x ∈ (x :: L) := by simp

/-- For any cycle with period p dividing L, (t+L) % p = t % p. -/
lemma mod_add_lcm {t p L : Nat} (hp : 0 < p) (hdiv : p ∣ L) :
    (t + L) % p = t % p := by
  rcases hdiv with ⟨k, rfl⟩
  -- (t + k*p) % p = t % p
  simpa [Nat.mod_add_mod, Nat.mul_comm] 

/-- c.p ∣ lcmFamily F when c ∈ F. -/
lemma dvd_lcmFamily_of_mem {F : Family} {c : Cycle} :
  c ∈ F → c.p ∣ lcmFamily F := by
  intro hc
  induction F with
  | nil => cases hc
  | cons d ds ih =>
    cases hc with
    | inl h =>
      cases h; 
      simpa [lcmFamily] using Nat.dvd_lcm_left d.p (lcmFamily ds)
    | inr hds =>
      have : c.p ∣ lcmFamily ds := ih hds
      have : c.p ∣ lcm d.p (lcmFamily ds) := Nat.dvd_trans this (Nat.dvd_lcm_right _ _)
      simpa [lcmFamily] using this

/-- Periodicity: Active(t+L) ↔ Active(t). -/
theorem active_periodic (F : Family) (t : Nat) :
  Active F (t + lcmFamily F) ↔ Active F t := by
  constructor <;> intro h
  all_goals
    rcases h with ⟨c, hcF, a, haA, hmod⟩
    have hdiv : c.p ∣ lcmFamily F := dvd_lcmFamily_of_mem (F:=F) (c:=c) hcF
    have hmod' := mod_add_lcm (t:=t) (p:=c.p) (L:=lcmFamily F) c.hp hdiv
    all_goals
      exact ⟨c, hcF, a, haA, by simpa [hmod'] using hmod⟩

/-- If Active is nonempty, then every window [t, t+L) contains an active time. -/
theorem bounded_gap (F : Family) (hNonempty : ∃ u, Active F u) :
  ∀ t, ∃ s, t ≤ s ∧ s < t + lcmFamily F ∧ Active F s := by
  intro t
  rcases hNonempty with ⟨u, hu⟩
  let L := lcmFamily F
  have hLpos : 0 < L := lcmFamily_pos F
  -- Consider s := u + k*L with k minimal such that s ≥ t
  let k := (t + L - u) / L
  let s := u + k * L
  have hk : t ≤ s := by
    have : (t + L - u) ≤ k * L + (t + L - u) % L := Nat.le_trans (Nat.le_refl _) (Nat.le_of_eq (Nat.ediv_add_emod ..).symm)
    have : t ≤ u + k*L + (t + L - u) % L := by
      have := Nat.add_le_add_left this u
      simpa [s, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    -- Since (t+L-u)%L < L, we have u + k*L ≤ t + L - 1 + u, hence s ≥ t.
    exact Nat.le_of_lt (lt_of_le_of_lt (Nat.le_of_lt_succ (Nat.lt_add_of_pos_right _ hLpos)) (Nat.lt_add_of_pos_right _ hLpos))
  -- Show s < t+L
  have hslt : s < t + L := by
    -- s = u + kL = t + L - r with r := (t+L-u) % L ∈ [0,L)
    have hdiv : (t+L-u) = k*L + ((t+L-u) % L) := Nat.ediv_add_emod _ _
    set r := (t+L-u) % L
    have rlt : r < L := Nat.mod_lt _ (Nat.ne_of_gt hLpos)
    have hs : s = t + L - r := by
      dsimp [s, k] at hdiv
      have := congrArg (fun x => u + x) hdiv
      simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.add_sub_cancel] using this
    have : t + L - r < t + L := Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.le_refl _) (lt_trans (Nat.lt_of_le_of_lt (Nat.le_refl _) rlt) (lt_of_le_of_lt (Nat.le_refl _) rlt))) (lt_trans (Nat.lt_of_le_of_lt (Nat.le_refl _) rlt) (lt_of_le_of_lt (Nat.le_refl _) rlt))
    simpa [hs] using this
  -- Active repeats every L; from hu get Active s
  have per : ∀ m, Active F (u + m*L) := by
    intro m
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      have := (active_periodic F (u + m*L)).mpr ih
      simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have hs : Active F s := by
    dsimp [s, k]; exact per _
  exact ⟨s, hk, hslt, hs⟩

end UFRF
