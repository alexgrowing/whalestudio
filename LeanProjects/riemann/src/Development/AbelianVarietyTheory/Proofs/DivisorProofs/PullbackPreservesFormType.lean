import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

set_option autoImplicit false

noncomputable section

open GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexConjugate

namespace GlobalTheory.CxForm.PullType

variable {n m : ℕ}

def scale (n : ℕ) (s t : ℂ) : Alt n →ₐ[ℂ] Alt n :=
  ExteriorAlgebra.map (Matrix.toLin' (Matrix.fromBlocks (s • 1) 0 0 (t • 1)))

theorem scale_single (s t : ℂ) (i : Fin (n + n)) :
    scale n s t (bas n {i}) = (if i.val < n then s else t) • bas n {i} := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [bas_singleton, ← map_smul]
  refine (ExteriorAlgebra.map_apply_ι _ _).trans (congrArg _ (funext ?_))
  rcases i with i | i <;> rintro (b | b) <;> simp [Pi.single_apply, Matrix.one_apply]

theorem scale_bas (s t : ℂ) (S : Finset (Fin (n + n))) :
    scale n s t (bas n S) = (s ^ (S.filter (·.val < n)).card * t ^ (S.filter (n ≤ ·.val)).card) • bas n S := by
  induction S using Finset.induction_on with
  | empty => simp [bas_empty]
  | insert a S ha ih =>
    obtain ⟨ε, h⟩ := bas_mul (n := n) (S := {a}) (T := S) (by simpa using ha)
    have h' : bas n (insert a S) = ε • (bas n {a} * bas n S) := by
      rw [h, smul_smul, Int.units_mul_self, one_smul, Finset.insert_eq]
    rw [h', Units.smul_def, map_zsmul, map_mul, scale_single, ih, smul_mul_smul_comm, smul_comm]
    congr 1
    rw [Finset.filter_insert, Finset.filter_insert]
    by_cases hn : a.val < n
    · rw [if_pos hn, if_pos hn, if_neg (not_le.2 hn), Finset.card_insert_of_notMem (by simp [ha])]
      ring
    · rw [if_neg hn, if_neg hn, if_pos (not_lt.1 hn), Finset.card_insert_of_notMem (by simp [ha])]
      ring

theorem repr_scale (s t : ℂ) (α : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (scale n s t α) S =
      (s ^ (S.filter (·.val < n)).card * t ^ (S.filter (n ≤ ·.val)).card) * (bas n).repr α S := by
  conv_lhs => rw [← (bas n).sum_repr α]
  simp only [map_sum, map_smul, scale_bas, Module.Basis.repr_self, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem isType_iff (p q : ℕ) (α : Alt n) :
    IsType p q α ↔ scale n 2 1 α = (2 : ℂ) ^ p • α ∧ scale n 1 2 α = (2 : ℂ) ^ q • α := by
  have h2 {a b : ℕ} (h : (2 : ℂ) ^ a = 2 ^ b) : a = b := by
    have : (2 : ℕ) ^ a = 2 ^ b := by exact_mod_cast h
    exact Nat.pow_right_injective le_rfl this
  constructor
  · intro h
    constructor <;> refine (bas n).ext_elem fun S => ?_ <;>
      rw [repr_scale, map_smul, Finsupp.smul_apply, smul_eq_mul] <;>
      by_cases hS : (bas n).repr α S = 0
    · simp [hS]
    · simp [(h S hS).1]
    · simp [hS]
    · simp [(h S hS).2]
  · rintro ⟨h₁, h₂⟩ S hS
    have e₁ := congrArg (fun β => (bas n).repr β S) h₁
    have e₂ := congrArg (fun β => (bas n).repr β S) h₂
    simp only [repr_scale, map_smul, Finsupp.smul_apply, smul_eq_mul, one_pow, mul_one, one_mul] at e₁ e₂
    exact ⟨h2 (mul_right_cancel₀ hS e₁), h2 (mul_right_cancel₀ hS e₂)⟩

theorem scale_pull (L : V n →L[ℂ] V m) (s t : ℂ) (α : Alt m) :
    scale n s t (pull L α) = pull L (scale m s t α) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, scale, scale, pull, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
  simp [Matrix.fromBlocks_multiply]

end GlobalTheory.CxForm.PullType

namespace GlobalTheory.CxForm

theorem isType_pull_linear (n m : ℕ) (L : V n →L[ℂ] V m) (p q : ℕ) (α : Alt m) (h : IsType p q α) :
    IsType p q (pull L α) := by
  rw [PullType.isType_iff] at h ⊢
  rw [PullType.scale_pull, PullType.scale_pull, h.1, h.2, map_smul, map_smul]
  exact ⟨rfl, rfl⟩

end GlobalTheory.CxForm
