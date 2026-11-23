import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.ThetaUnfoldInt

theorem integral_fundamentalDomain_tsum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ (μ : MeasureTheory.Measure (κ → AF F)), μ.IsAddHaarMeasure →
    ∀ 𝓕₁ : Set (κ → AF F), MeasureTheory.IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ →
    ∀ h : (κ → AF F) → ℂ, Continuous h →
      (∃ B : ℝ, ∀ x : κ → AF F, Summable (fun η : κ → F => ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖) ∧
        ∑' η : κ → F, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ ≤ B) →
      ∫ x in 𝓕₁, ∑' η : κ → F, h ((fun i => algebraMap F (AF F) (η i)) + x) ∂μ = ∫ u, h u ∂μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AF F) := borel _
  intro μ hμ 𝓕₁ h𝓕 hfin h hc hB
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨B, hB⟩ := hB
  haveI : Countable F := by
    have b := Module.finBasis ℚ F
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI : Countable (GlobalTheory.ThetaParseval.ratVec F κ) := Countable.of_equiv _ (GlobalTheory.ThetaUnfold.ratEquiv F κ)
  have hcont : ∀ η : κ → F, Continuous fun x => h ((fun i => algebraMap F (AF F) (η i)) + x) :=
    fun η => hc.comp (continuous_const.add continuous_id)
  have hreidx : ∀ f : (κ → AF F) → ENNReal,
      ∫⁻ x, f x ∂μ = ∑' η : κ → F, ∫⁻ x in 𝓕₁, f ((fun i => algebraMap F (AF F) (η i)) + x) ∂μ := by
    intro f
    rw [h𝓕.lintegral_eq_tsum' f, ← ((GlobalTheory.ThetaUnfold.ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
    refine tsum_congr fun ξ => ?_
    simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
    rfl
  have hpt : ∀ x, ∑' η : κ → F, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ₑ ≤ ENNReal.ofReal B := by
    intro x
    obtain ⟨hs, hle⟩ := hB x
    simp_rw [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
    exact ENNReal.ofReal_le_ofReal hle
  have hfinite : ∑' η : κ → F, ∫⁻ x in 𝓕₁, ‖h ((fun i => algebraMap F (AF F) (η i)) + x)‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum fun η => (hcont η).measurable.enorm.aemeasurable]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hint : Integrable h μ := by
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    show ∫⁻ a, ‖h a‖ₑ ∂μ < ⊤
    rw [hreidx fun a => ‖h a‖ₑ]
    exact hfinite.lt_top
  rw [integral_tsum (fun η => (hcont η).aestronglyMeasurable) hfinite,
    h𝓕.integral_eq_tsum' h hint, ← ((GlobalTheory.ThetaUnfold.ratEquiv F κ).trans (Equiv.neg _)).tsum_eq]
  refine tsum_congr fun ξ => ?_
  simp only [Equiv.trans_apply, Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add]
  rfl

end GlobalTheory.ThetaUnfoldInt

end
