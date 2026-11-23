import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerSide
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsConeTrdegFnField
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDvrConeDimTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal joinCoord fnField)

namespace JoinTwoModels

section Field

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

theorem ratio_mem {K' : Type} {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : fnField O (joinCoord x z) = fnField O x) (k : K') (i j : ι' k) :
    z ⟨k, i⟩ / z ⟨k, j⟩ ∈ fnField O x := by
  rw [← h]
  exact Subfield.subset_closure (Or.inr ⟨⟨.inr k, (i, j)⟩, rfl⟩)

theorem fnField_join_two {K₁ : Type} {ι₁ : K₁ → Type} {K₂ : Type} {ι₂ : K₂ → Type} (x : (Σ k, ι k) → Ω)
    (z₁ : (Σ k, ι₁ k) → Ω) (z₂ : (Σ k, ι₂ k) → Ω) (h₁ : fnField O (joinCoord x z₁) = fnField O x)
    (h₂ : fnField O (joinCoord x z₂) = fnField O x) :
    fnField O (joinCoord x (joinCoord z₁ z₂)) = fnField O x := by
  apply le_antisymm
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨kk, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    · rcases kk with k | k | k
      · exact Subfield.subset_closure (Or.inr ⟨⟨k, (i, j)⟩, rfl⟩)
      · exact ratio_mem x z₁ h₁ k i j
      · exact ratio_mem x z₂ h₂ k i j
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, (i, j)⟩, rfl⟩)

end Field

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem exists_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    {d : ℕ} (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  classical
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at h
  obtain ⟨j, hj⟩ := h.2.multiProj.relevant k
  refine ⟨j, fun h0 => hj ?_⟩
  rw [pointIdeal, RingHom.mem_ker]
  simp [pointConeMap, h0]

end Model

end JoinTwoModels

open JoinTwoModels in

theorem JoinTwoModels.proof (hC : ConeTrdegFnField.Statement) : JoinTwoModels.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d hx K₁ _ ι₁ _ z₁ K₂ _ ι₂ _ z₂ h₁ hf₁ h₂ hf₂
  classical
  have hf := fnField_join_two x z₁ z₂ hf₁ hf₂
  refine ⟨?_, hf⟩
  have hy : ∀ k, ∃ i, joinCoord x (joinCoord z₁ z₂) ⟨k, i⟩ ≠ 0 := by
    rintro (k | k | k)
    · exact exists_ne_zero x hx k
    · exact exists_ne_zero _ h₁ (.inr k)
    · exact exists_ne_zero _ h₂ (.inr k)
  have hx' : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := exists_ne_zero x hx
  have hxW := hx
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at hxW
  obtain ⟨hK, hW⟩ := hxW
  have hinj : Function.Injective (algebraMap O Ω) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O x).comap (C : O →+* MRing ι O) := by
      simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
        MvPolynomial.algebraMap_apply, ha, map_zero]
    rw [hW.noTorsion] at hmem
    exact hmem
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff]
  have hP := GenericProjClosureDim.isMultiProjPrime_pointIdeal (R := O) _ hy
  have hPC : (pointIdeal O (joinCoord x (joinCoord z₁ z₂))).comap
      (C : O →+* MRing (Sum.elim ι (Sum.elim ι₁ ι₂)) O) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [← hW.noTorsion]
    simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
      MvPolynomial.algebraMap_apply, C_eq_zero] at ha ⊢
    exact ha
  refine ⟨inferInstance, ⟨hP, hPC, ?_⟩⟩

  have hdW := DvrConeDimTrdeg.proof O K ι (pointIdeal O x) hW.multiProj hW.noTorsion
  have hdJ := DvrConeDimTrdeg.proof O (K ⊕ (K₁ ⊕ K₂)) (Sum.elim ι (Sum.elim ι₁ ι₂)) _ hP hPC
  have htW := hC O Ω hinj K ι x hx'
  have htJ := hC O Ω hinj (K ⊕ (K₁ ⊕ K₂)) (Sum.elim ι (Sum.elim ι₁ ι₂)) _ hy
  rw [hf] at htJ
  rw [BundleExamples.mcIdeal_eq_pointIdeal] at htW htJ
  set T := Algebra.trdeg O (Algebra.adjoin O (fnField O x : Set Ω))
  rw [hW.dim] at hdW
  erw [htW] at hdW
  erw [hdJ, htJ]
  rw [map_add, map_natCast] at hdW ⊢
  have hT : Cardinal.toENat T = d := by
    have h1 : ((Cardinal.toENat T + (Fintype.card K : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) =
        ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdW.symm
    have h2 : Cardinal.toENat T + ((Fintype.card K + 1 : ℕ) : ℕ∞) = (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
      have := WithBot.coe_injective h1
      push_cast at this ⊢
      rw [← add_assoc, this]; ring
    exact (WithTop.add_right_cancel (ENat.natCast_ne_top _) h2)
  rw [hT, Fintype.card_sum, Fintype.card_sum]
  have e : ((d : ℕ∞) + ((Fintype.card K + (Fintype.card K₁ + Fintype.card K₂) : ℕ) : ℕ∞) + 1) =
      ((d + 1 + (Fintype.card K + (Fintype.card K₁ + Fintype.card K₂)) : ℕ) : ℕ∞) := by
    push_cast; ring
  rw [e]
  norm_cast

end GroundTheory.Heights₂.Heights.NumbersDVR
