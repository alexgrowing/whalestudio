import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

set_option autoImplicit false

open GlobalTheory.CxForm

namespace GlobalTheory.ExactZero

theorem eq_algebraMap_of_isType {n : ℕ} {a : Alt n} (h : IsType 0 0 a) : ∃ c : ℂ, a = algebraMap ℂ (Alt n) c := by
  refine ⟨(bas n).repr a ∅, (bas n).ext_elem fun S => ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, ← bas_empty, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  split_ifs with hS
  · rw [← hS, smul_eq_mul, mul_one]
  · rw [smul_zero]
    by_contra h0
    obtain ⟨h₁, h₂⟩ := h S h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h₁ h₂
    refine hS (Finset.eq_empty_of_forall_notMem fun i hi => ?_).symm
    exact h₂ hi (not_lt.1 (h₁ hi))

theorem algebraMapInv_delAt {n : ℕ} (u : ReciprocityTheory.L2DbarEstimates.V n → Alt n) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    ExteriorAlgebra.algebraMapInv (delAt u v) = 0 := by
  simp [delAt, dz, map_sum, ExteriorAlgebra.algebraMapInv]

theorem algebraMapInv_dbarAt {n : ℕ} (u : ReciprocityTheory.L2DbarEstimates.V n → Alt n) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    ExteriorAlgebra.algebraMapInv (dbarAt u v) = 0 := by
  simp [dbarAt, dzb, map_sum, ExteriorAlgebra.algebraMapInv]

theorem eq_of_isExact_sub : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α β : A.Fld),
    (∀ x, IsType 0 0 (α x)) → (∀ x, IsType 0 0 (β x)) → A.IsExact (α - β) → α = β := by
  intro M _ n A α β hα hβ ⟨u, w, _, _, e⟩
  funext x
  obtain ⟨c, hc⟩ := eq_algebraMap_of_isType (hα x)
  obtain ⟨d, hd⟩ := eq_algebraMap_of_isType (hβ x)
  have h := congrArg (fun γ : A.Fld => ExteriorAlgebra.algebraMapInv (γ x)) e
  simp only [Pi.sub_apply, Pi.add_apply, HolAtlas.del, HolAtlas.dbar, map_add, map_sub, algebraMapInv_delAt,
    algebraMapInv_dbarAt, hc, hd, AlgHom.commutes, add_zero, sub_eq_zero] at h
  rw [hc, hd]
  exact congrArg _ h

end GlobalTheory.ExactZero
