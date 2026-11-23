import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GoodOfMemSlots

open Formalism.L2.FormalSeriesBounds GlobalTheory.LeafTerm

namespace GlobalTheory.FrobRoot

variable {C : Type} [Field C] {V : VF C}

def intRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos

theorem mm_of_ge_one {a : C} (ha : V.Ge 1 a) : V.MM a := by
  refine lt_of_lt_of_le ?_ ha
  exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)

theorem mm_pow {a : C} (ha : V.MM a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) := by
  unfold VF.MM at *
  rw [V.v.map_pow]
  exact nsmul_pos ha hn

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (ha : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  unfold VF.Ge at *
  rw [V.v.map_pow] at ha
  rw [WithTop.coe_zero] at ha ⊢
  by_contra h
  exact absurd ha (not_le.mpr (nsmul_neg (not_le.mp h) hn))

theorem mm_add_pow (e : ℕ) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.MM ((a + b) ^ (V.l ^ e) - (a ^ (V.l ^ e) + b ^ (V.l ^ e))) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime
    (⟨a, ha⟩ : intRing V) (⟨b, hb⟩ : intRing V) e
  have h := congrArg (Subtype.val) hr
  push_cast at h
  rw [h, add_sub_cancel_left]
  apply mm_of_ge_one
  have hr0 : V.Ge 0 (r : C) := r.2
  first
    | simpa using hr0.l_mul
    | simpa [mul_assoc] using (ha.mul_int (hb.mul_int hr0)).l_mul

theorem mm_sum_pow (e : ℕ) {ι : Type} (s : Finset ι) (x : ι → C) (hx : ∀ i ∈ s, V.Ge 0 (x i)) :
    V.MM ((∑ i ∈ s, x i) ^ (V.l ^ e) - ∑ i ∈ s, x i ^ (V.l ^ e)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero e V.l_prime.ne_zero), sub_zero]
    exact mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : ∀ i ∈ s, V.Ge 0 (x i) := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have h := mm_add (mm_add_pow e (hx a (Finset.mem_insert_self a s)) (VF.Ge.sum hs)) (ih hs)
    convert h using 1
    ring

end GlobalTheory.FrobRoot
