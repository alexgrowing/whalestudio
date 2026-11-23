import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTorusActionRot

set_option autoImplicit false

noncomputable section

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.CxForm

def holCount {n : ℕ} (S : Finset (Fin (n + n))) : ℕ := (S.filter (·.val < n)).card

def holGe (n p : ℕ) : Submodule ℂ (Alt n) :=
  Submodule.span ℂ (bas n '' {S | p ≤ holCount S})

theorem mem_holGe_iff {n p : ℕ} (β : Alt n) :
    β ∈ holGe n p ↔ ∀ S, (bas n).repr β S ≠ 0 → p ≤ holCount S := by
  rw [holGe, Module.Basis.mem_span_image]
  constructor
  · intro h S hS
    exact h (Finsupp.mem_support_iff.2 hS)
  · intro h S hS
    exact h S (Finsupp.mem_support_iff.1 hS)

theorem holGe_anti {n p q : ℕ} (h : p ≤ q) : holGe n q ≤ holGe n p :=
  Submodule.span_mono (Set.image_mono fun _ hS => le_trans h hS)

theorem bas_mem_holGe {n : ℕ} (S : Finset (Fin (n + n))) : bas n S ∈ holGe n (holCount S) :=
  Submodule.subset_span ⟨S, show holCount S ≤ holCount S from le_refl _, rfl⟩

theorem bas_insert_eq {n : ℕ} {a : Fin (n + n)} {s : Finset (Fin (n + n))} (h : a ∉ s) :
    ∃ ε : ℤˣ, bas n (insert a s) = ε • (bas n {a} * bas n s) := by
  obtain ⟨ε, e⟩ := bas_mul (n := n) (S := {a}) (T := s) (Finset.disjoint_singleton_left.2 h)
  refine ⟨ε, ?_⟩
  rw [e, smul_smul, Int.units_mul_self, one_smul, Finset.insert_eq]

theorem holCount_insert {n : ℕ} {a : Fin (n + n)} {s : Finset (Fin (n + n))} (h : a ∉ s) :
    holCount (insert a s) = holCount s + if a.val < n then 1 else 0 := by
  unfold holCount
  rw [Finset.filter_insert]
  split_ifs with ha
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1)]
  · simp

theorem bas_single_mul_self {n : ℕ} (a : Fin (n + n)) : bas n {a} * bas n {a} = 0 := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective a
  rw [bas_singleton]
  exact ExteriorAlgebra.ι_sq_zero _

theorem bas_single_mul_bas {n : ℕ} (a : Fin (n + n)) (T : Finset (Fin (n + n))) :
    bas n {a} * bas n T ∈ holGe n (holCount T + if a.val < n then 1 else 0) := by
  by_cases h : a ∈ T
  · obtain ⟨ε, e⟩ := bas_insert_eq (Finset.notMem_erase a T)
    rw [Finset.insert_erase h] at e
    rw [e, mul_smul_comm, ← mul_assoc, bas_single_mul_self, zero_mul, smul_zero]
    exact zero_mem _
  · obtain ⟨ε, e⟩ := bas_mul (n := n) (S := {a}) (T := T) (Finset.disjoint_singleton_left.2 h)
    rw [e, ← Finset.insert_eq, ← holCount_insert h, Units.smul_def]
    exact zsmul_mem (bas_mem_holGe _) _

theorem bas_single_mul_mem {n : ℕ} (a : Fin (n + n)) {q : ℕ} {y : Alt n} (hy : y ∈ holGe n q) :
    bas n {a} * y ∈ holGe n (q + if a.val < n then 1 else 0) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    exact holGe_anti (Nat.add_le_add_right hT _) (bas_single_mul_bas a T)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hx

theorem pull_bas_mem {n m : ℕ} (L : V n →L[ℂ] V m) (S : Finset (Fin (m + m))) :
    pull L (bas m S) ∈ holGe n (holCount S) := by
  induction S using Finset.induction_on with
  | empty =>
    have h0 : holCount (∅ : Finset (Fin (m + m))) = 0 := by simp [holCount]
    rw [bas_empty, map_one, h0, ← bas_empty]
    exact holGe_anti (Nat.zero_le _) (bas_mem_holGe _)
  | insert a s ha ih =>
    obtain ⟨ε, e⟩ := bas_insert_eq ha
    rw [e, holCount_insert ha, Units.smul_def, map_zsmul, map_mul]
    refine zsmul_mem ?_ _
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective a
    rw [bas_singleton]
    rcases i with i | i
    · have hi : (finSumFinEquiv (Sum.inl i : Fin m ⊕ Fin m)).val < m := by simp
      rw [if_pos hi, show ExteriorAlgebra.ι ℂ (Pi.single (Sum.inl i) 1) = dz (n := m) i from rfl, (pull_dz L i).1,
        Finset.sum_mul]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ _ ?_
      have hb : (finSumFinEquiv (Sum.inl b : Fin n ⊕ Fin n)).val < n := by simp
      have := bas_single_mul_mem (finSumFinEquiv (Sum.inl b)) ih
      rwa [if_pos hb, bas_singleton] at this
    · have hi : ¬ (finSumFinEquiv (Sum.inr i : Fin m ⊕ Fin m)).val < m := by simp
      rw [if_neg hi, show ExteriorAlgebra.ι ℂ (Pi.single (Sum.inr i) 1) = dzb (n := m) i from rfl, (pull_dz L i).2,
        Finset.sum_mul]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ _ ?_
      have hb : ¬ (finSumFinEquiv (Sum.inr b : Fin n ⊕ Fin n)).val < n := by simp
      have := bas_single_mul_mem (finSumFinEquiv (Sum.inr b)) ih
      rwa [if_neg hb, bas_singleton] at this

theorem pull_mem_holGe {n m : ℕ} (L : V n →L[ℂ] V m) {p : ℕ} {β : Alt m} (h : β ∈ holGe m p) :
    pull L β ∈ holGe n p := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, hS, rfl⟩ := hx
    exact holGe_anti hS (pull_bas_mem L S)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

end GlobalTheory.CxForm
