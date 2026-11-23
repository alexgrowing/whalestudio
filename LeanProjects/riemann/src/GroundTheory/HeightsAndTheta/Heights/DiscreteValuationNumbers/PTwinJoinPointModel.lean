import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerMore
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord joinCoord mcMap)

namespace JoinPointModel

section Split

variable {K : Type} {ι : K → Type}

def varEquiv : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Option (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  invFun
    | some p => ⟨.inl p.1, p.2⟩
    | none => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨k | u, i⟩
    · rfl
    · cases u
      change Fin 1 at i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rfl
  right_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl

variable (K) (Ω : Type*) [CommRing Ω]

def tgtEquiv : MvPolynomial (K ⊕ Unit) Ω ≃ₐ[Ω] Polynomial (MvPolynomial K Ω) :=
  (renameEquiv Ω (Equiv.optionEquivSumPUnit.{0, 0} K).symm).trans (optionEquivLeft Ω K)

variable {K} (O : Type*) [CommRing O]

def srcEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O ≃ₐ[O]
    Polynomial (MvPolynomial (Σ k, ι k) O) :=
  (renameEquiv O varEquiv).trans (optionEquivLeft O _)

end Split

section Cone

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem tgtEquiv_mcMap (y : (Σ k, ι k) → Ω) (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    tgtEquiv K Ω (mcMap O (joinCoord y (ptCoord (Ω := Ω))) p) =
      Polynomial.map (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω) (srcEquiv O p) := by
  have h : ((tgtEquiv K Ω : MvPolynomial (K ⊕ Unit) Ω →+* Polynomial (MvPolynomial K Ω)).comp
      (mcMap O (joinCoord y (ptCoord (Ω := Ω))) : _ →+* MvPolynomial (K ⊕ Unit) Ω)) =
      (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)).comp
        (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tgtEquiv, srcEquiv, mcMap, optionEquivLeft_C]
    · rintro ⟨k | u, i⟩
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, optionEquivLeft_X_some, optionEquivLeft_C]
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, ptCoord, optionEquivLeft_X_none]
  exact RingHom.congr_fun h p

theorem mem_pointIdeal_join_iff (y : (Σ k, ι k) → Ω)
    (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    p ∈ pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) ↔
      srcEquiv O p ∈ RingHom.ker
        (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)) := by
  rw [← BundleExamples.mcIdeal_eq_pointIdeal, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, RingHom.mem_ker, RingHom.mem_ker,
    Polynomial.coe_mapRingHom, ← tgtEquiv_mcMap, map_eq_zero_iff _ (tgtEquiv K Ω).injective]

theorem ringKrullDim_join [IsNoetherianRing O] (y : (Σ k, ι k) → Ω) :
    ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ pointIdeal O (joinCoord y (ptCoord (Ω := Ω)))) =
      ringKrullDim (MRing ι O ⧸ pointIdeal O y) + 1 := by
  let J := RingHom.ker (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω))
  let Φ : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O →+* Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J :=
    (Ideal.Quotient.mk J).comp (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom
  have hΦ : Function.Surjective Φ := Ideal.Quotient.mk_surjective.comp (srcEquiv O).surjective
  have hker : pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) = RingHom.ker Φ := by
    ext p
    rw [mem_pointIdeal_join_iff, RingHom.mem_ker (f := Φ)]
    change _ ↔ Ideal.Quotient.mk J (srcEquiv O p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
  have hJ : J = (pointIdeal O y).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) := by
    simp only [J]
    rw [Polynomial.ker_mapRingHom]
    rfl
  have hq : ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ RingHom.ker Φ) =
      ringKrullDim (Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hΦ)
  have hp : ringKrullDim (Polynomial (MRing ι O ⧸ pointIdeal O y)) =
      ringKrullDim (Polynomial (MRing ι O) ⧸ (pointIdeal O y).map (Polynomial.C : MRing ι O →+* _)) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.polynomialQuotientEquivQuotientPolynomial (pointIdeal O y))
  rw [hker, hq, hJ, ← hp, Polynomial.ringKrullDim_of_isNoetherianRing]

end Cone

end JoinPointModel

open JoinPointModel in

theorem JoinPointModel.proof : JoinPointModel.Statement := by
  intro O _ _ _ Ω _ _ K _ _ ι _ y d hW
  rw [BundleExamples.isModelOver_iff]
  refine ⟨inferInstance, ⟨?_, ?_, ?_⟩⟩
  · apply GenericProjClosureDim.isMultiProjPrime_pointIdeal
    rintro (k | u)
    · obtain ⟨j, hj⟩ := hW.multiProj.relevant k
      refine ⟨j, fun h0 => hj ?_⟩
      change y ⟨k, j⟩ = 0 at h0
      rw [pointIdeal, RingHom.mem_ker]
      simp [pointConeMap, h0]
    · exact ⟨(0 : Fin 1), by simp [joinCoord, ptCoord]⟩
  · rw [eq_bot_iff]
    intro a ha
    rw [← hW.noTorsion]
    simp only [Ideal.mem_comap, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, pointIdeal, RingHom.mem_ker,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, C_eq_zero] at ha ⊢
    exact ha
  · rw [BundleExamples.mcIdeal_eq_pointIdeal, ringKrullDim_join, hW.dim, Fintype.card_sum, Fintype.card_unit,
      show d + 1 + (Fintype.card K + 1) = (d + 1 + Fintype.card K) + 1 by omega]
    norm_cast

end GroundTheory.Heights₂.Heights.NumbersDVR
