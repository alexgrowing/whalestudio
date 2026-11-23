import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory

open NumberField IsDedekindDomain Matrix in
private theorem sum_smulRight_finBasis_mul_smulRight_eq_one {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (w : W) (ℓ : Module.Dual ℂ W) (h : ℓ w = 1) :
    ∑ i, ℓ.smulRight (Module.finBasis ℂ W i) * ((Module.finBasis ℂ W).coord i).smulRight w = 1 := by
  ext x
  simpa [h] using (Module.finBasis ℂ W).sum_repr x

open NumberField IsDedekindDomain Matrix in
private theorem exists_dual_algHom_smulRight_apply_ne_zero {W V : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [AddCommGroup V] [Module ℂ V] (w : W) (ℓ : Module.Dual ℂ W)
    (h : ℓ w = 1) (Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V) {y : V} (hy : y ≠ 0) :
    ∃ φ : Module.Dual ℂ W, Φ (φ.smulRight w) y ≠ 0 := by
  by_contra! hzero
  apply hy
  calc y = Φ 1 y := by simp
    _ = ∑ i, Φ (ℓ.smulRight (Module.finBasis ℂ W i))
          (Φ (((Module.finBasis ℂ W).coord i).smulRight w) y) := by
        rw [← sum_smulRight_finBasis_mul_smulRight_eq_one w ℓ h, map_sum, LinearMap.sum_apply]
        simp only [map_mul, Module.End.mul_apply]
    _ = 0 := by simp [hzero]

open NumberField IsDedekindDomain Matrix in
private theorem smulRight_mul_smulRight_of_apply_eq_one {W : Type} [AddCommGroup W] [Module ℂ W]
    (w : W) (ℓ φ : Module.Dual ℂ W) (h : ℓ w = 1) :
    ℓ.smulRight w * φ.smulRight w = φ.smulRight w := by
  ext x
  simp [h]

open NumberField IsDedekindDomain Matrix in

theorem _root_.GlobalTheory.commuting_endAlgebras_common_fixed_vector :
    ∀ (ι : Type) [Fintype ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)]
      [∀ v, FiniteDimensional ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V]
      (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v)
      (ℓ : ∀ v, Module.Dual ℂ (Wv v)), Nontrivial V → (∀ v, ℓ v (w v) = 1) →
      (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) →
      ∃ y : V, y ≠ 0 ∧ ∀ v, Φ v ((ℓ v).smulRight (w v)) y = y := by
  intro ι _ Wv _ _ _ V _ _ Φ w ℓ _ hℓ hcomm
  classical
  have key : ∀ s : Finset ι, ∃ y : V, y ≠ 0 ∧ ∀ v ∈ s, Φ v ((ℓ v).smulRight (w v)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨y, hy⟩ := exists_ne (0 : V)
      exact ⟨y, hy, by simp⟩
    | insert v s hv ih =>
      obtain ⟨y, hy0, hy⟩ := ih
      obtain ⟨φ, hφ⟩ := exists_dual_algHom_smulRight_apply_ne_zero (w v) (ℓ v) (hℓ v) (Φ v) hy0
      refine ⟨Φ v (φ.smulRight (w v)) y, hφ, fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hu
      · rw [← Module.End.mul_apply, ← map_mul,
          smulRight_mul_smulRight_of_apply_eq_one _ _ _ (hℓ u)]
      · have huv : u ≠ v := fun h => hv (h ▸ hu)
        rw [← Module.End.mul_apply, (hcomm u v huv _ _).eq, Module.End.mul_apply, hy u hu]
  obtain ⟨y, hy0, hy⟩ := key Finset.univ
  exact ⟨y, hy0, fun v => hy v (Finset.mem_univ v)⟩

end GlobalTheory
