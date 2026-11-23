import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.SmulOfEqOfMemFixingSubgroup
import GroundTheory.GlobalFields.IdeleClassGroup.Invariants
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleLimit

open FiniteSubfield

theorem smul_of_eq_of_ideleEquiv {M : FiniteSubfield} (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (τ : M.1 ≃+* M.1)
    (h : ∀ x : M.1, σ x = τ x) (x : IdeleGroup M.1) :
    σ • of M x = of M (ideleEquiv τ x) :=
  (smul_of σ M x).trans (of_ideleEquiv_congr _ _ h x)

theorem mem_range_of_of_forall_smul_eq (F : FiniteSubfield) (z : IdeleLimit)
    (hz : ∀ σ ∈ F.1.fixingSubgroup, σ • z = z) : z ∈ (of F).range := by
  obtain ⟨E, x, rfl⟩ := exists_of z
  let S : FiniteSubfield := ⟨F.1 ⊔ E.1, inferInstance⟩
  let M := galoisClosure S
  have hFM : F ≤ M := le_trans (show F.1 ≤ F.1 ⊔ E.1 from le_sup_left) (le_galoisClosure S)
  have hEM : E ≤ M := le_trans (show E.1 ≤ F.1 ⊔ E.1 from le_sup_right) (le_galoisClosure S)
  rw [← of_ideleMap hEM x] at hz ⊢
  let := algebraOfLE hFM
  have : IsScalarTower ℚ F.1 M.1 := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : IsGalois F.1 M.1 := IsGalois.tower_top_of_isGalois ℚ F.1 M.1
  have hfix : ∀ σ : M.1 ≃ₐ[F.1] M.1, σ • ideleMap hEM x = ideleMap hEM x := by
    intro σ
    let σ' : ℚ̄ ≃ₐ[ℚ] ℚ̄ := (σ.restrictScalars ℚ).liftNormal ℚ̄
    have hσ' : ∀ y : M.1, σ' y = σ y := fun y ↦ (σ.restrictScalars ℚ).liftNormal_commutes ℚ̄ y
    have hmem : σ' ∈ F.1.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h1 := hσ' (algebraMap F.1 M.1 ⟨y, hy⟩)
      rw [σ.commutes] at h1
      exact h1
    have h1 := hz σ' hmem
    rw [smul_of_eq_of_ideleEquiv σ' (σ : M.1 ≃+* M.1) hσ'] at h1
    rw [smul_idele_eq_ideleEquiv]
    exact of_injective M h1
  obtain ⟨d, hd⟩ := (forall_smul_eq_iff_mem_range_ideleEmbedding (K := F.1) (ideleMap hEM x)).1 hfix
  exact ⟨d, by rw [← of_ideleMap hFM d]; exact congrArg (of M) hd⟩

end IdeleLimit

end

end GroundTheory.ProfCoh
