import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreExtra
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalComponentFibre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFibreVarieties
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericFibProps
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimBound
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMaximalIdealHeightFG
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimGe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PComponentDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomogIdeal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalDivisorSupportFibre.fibreVarieties : FibreVarieties.Statement.{0} :=
  FibreVarieties.proof GenericFibProps.proof (GenericDimBound.proof MaximalIdealHeightFG.proof)
    GenericDimGe.proof SpecialIdealCorresp.proof SpecialIdealMultiHomog.proof SupSpanMultiHomog.proof
    MinimalPrimeMultiHomog.proof SpecialQuotDim.proof ComponentDim.proof

theorem VerticalDivisorSupportFibre.proof : VerticalDivisorSupportFibre.Statement := by
  classical
  intro O _ _ _ K _ ι _ P d hP b f g hV W hW
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hP1⟩ := (BundleExamples.isModelOver_iff O P d).mp hP
  have hV1 := (VerticalDivisorCharacterisation.proof O K ι P ϖ b f g hϖ hP1.multiProj).mp hV
  rw [BundleExamples.ratCyc_eq] at hW
  have hϖW := hV1.vertical W hW
  rw [BundleExamples.redIdeal_eq]

  have key : ∀ (h : MRing ι O) (bh : K → ℕ), IsMultiHomog h bh → h ∉ P → divCycle P h W ≠ 0 →
      ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d := by
    intro h bh hh hhP hne
    unfold divCycle at hne
    split_ifs at hne with hc
    · obtain ⟨hmp, hdim⟩ := VerticalComponentFibre.proof VerticalDivisorSupportFibre.fibreVarieties O ϖ hϖ
        K ι P d hP1 h bh hh hhP W hc.1 hc.2 hϖW
      obtain ⟨hpr, hho, hre⟩ := hmp
      exact ⟨⟨hpr, (VocabMultiHomogIdeal.proof VocabMultiHomog.proof _ K ι _).2 hho, hre⟩, hdim⟩
    · exact absurd rfl hne
  obtain ⟨bf, bg, hf, hg, -⟩ := hV1.degrees
  by_cases hfW : divCycle P f W = 0
  · refine key g bg hg hV1.den_not_mem fun hgW => hW ?_
    simp [ratDiv, hfW, hgW]
  · exact key f bf hf hV1.num_not_mem hfW

end GroundTheory.Heights₂.Heights.NumbersDVR
