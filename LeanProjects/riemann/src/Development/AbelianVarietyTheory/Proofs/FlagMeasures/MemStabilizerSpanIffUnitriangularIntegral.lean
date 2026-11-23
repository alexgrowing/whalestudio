import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
open Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise

namespace GlobalTheory.HL

theorem span_pointwise_le_of_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E)
    (h : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E) (hM : IsIntM L M)
    (hv : ∀ b, h (v b) = ∑ a, M a b • v a) :
    h • Submodule.span L.O (Set.range v) ≤ Submodule.span L.O (Set.range v) := by
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  show h (v b) ∈ _
  rw [hv b]
  refine Submodule.sum_mem _ fun a _ => ?_
  have : M a b • v a = (⟨M a b, hM a b⟩ : L.O) • v a := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem unistab_iff : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N m : ℕ} (v : Fin m → Fin N → E), LinearIndependent E v → ∀ (g : (Fin N → E) ≃ₗ[E] (Fin N → E)) (M : Matrix (Fin m) (Fin m) E), IsUni M → (∀ b, g (v b) = ∑ a, M a b • v a) → (g ∈ MulAction.stabilizer ((Fin N → E) ≃ₗ[E] (Fin N → E)) (Submodule.span L.O (Set.range v)) ↔ IsIntM L M) := by
  intro F _ _ _ E _ _ _ L N m v hli g M hU hg
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hst a b
    have hmem : g (v b) ∈ Submodule.span L.O (Set.range v) := by
      rw [← hst]
      exact Submodule.smul_mem_pointwise_smul (v b) g _ (Submodule.subset_span ⟨b, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hmem
    rw [hg b] at hc
    have h0 : ∑ i, (M i b - (c i : E)) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hc]
      simp [Subring.smul_def]
    have := (Fintype.linearIndependent_iff.1 hli) _ h0 a
    rw [sub_eq_zero] at this
    rw [this]
    exact (c a).2
  · intro hM
    have hdet : M.det = 1 := by
      rw [Matrix.det_of_upperTriangular (fun i j hij => hU.1 i j hij)]
      simp [hU.2]
    let M₀ : Matrix (Fin m) (Fin m) L.O := fun i j => ⟨M i j, hM i j⟩
    have hM₀ : M₀.map L.O.subtype = M := by ext i j; rfl
    have hadj : IsIntM L M.adjugate := by
      intro i j
      have e := congrFun (congrFun (RingHom.map_adjugate L.O.subtype M₀) i) j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
      rw [hM₀] at e
      rw [← e]
      exact (M₀.adjugate i j).2
    have hinv : ∀ b, g⁻¹ (v b) = ∑ a, M.adjugate a b • v a := by
      intro b
      have key : g (∑ a, M.adjugate a b • v a) = v b := by
        simp only [map_sum, map_smul, hg, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        have : ∀ c, ∑ a, (M.adjugate a b * M c a) • v c = (M * M.adjugate) c b • v c := by
          intro c
          rw [← Finset.sum_smul, Matrix.mul_apply]
          congr 1
          exact Finset.sum_congr rfl fun a _ => mul_comm _ _
        simp only [this, Matrix.mul_adjugate, hdet, one_smul]
        simp [Matrix.one_apply]
      rw [← key]
      exact g.symm_apply_apply _
    apply le_antisymm
    · exact span_pointwise_le_of_int L v g M hM hg
    · intro x hx
      have hx' : g⁻¹ • x ∈ Submodule.span L.O (Set.range v) :=
        span_pointwise_le_of_int L v g⁻¹ M.adjugate hadj hinv
          (Submodule.smul_mem_pointwise_smul x g⁻¹ _ hx)
      have := Submodule.smul_mem_pointwise_smul (g⁻¹ • x) g _ hx'
      rwa [smul_inv_smul] at this

end GlobalTheory.HL
