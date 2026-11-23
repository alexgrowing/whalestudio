import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightBruhatFundamentalDomainCentralizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSubgroupConjugacyClassEqTsumWeightedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassTermConvergesOfLintegralUnfoldingEqStatement

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ClassUnfold

theorem hasClassInt_of_hasOrbInt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), γ ∈ Γ → IsMulCommutative (cent γ) →
    ∀ (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)),
    IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt → dt 𝓣 < ⊤ →
    ∀ (f : H → ℂ) (c : ℂ), Continuous f → HasCompactSupport f → HasOrbInt μ γ dt f c →
    ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt Γ μ 𝓕 γ f (dt.real 𝓣 * c) := by
  intro H _ _ _ _ _ _ _ _ Γ _ γ hγ hc μ _ dt _ 𝓣 h𝓣 hfin f c hf hfc hO 𝓕 h𝓕
  obtain ⟨α, hαm, hα1, hαI⟩ := GlobalTheory.T.exists_weight_bruhat_fundamental_domain_centralizer H Γ γ hc μ dt 𝓣 h𝓣
  have hL : ∀ G : H → ℝ≥0∞, Measurable G →
      ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ =
        dt 𝓣 * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂(quotMeas (cent γ) dt μ) := by
    intro G hG
    have hψ : Measurable fun y : H => G (y⁻¹ * γ * y) := hG.comp (by fun_prop)
    have hinv : LeftInv (cent γ) fun y : H => G (y⁻¹ * γ * y) := fun t ht y => by
      have : (t * y)⁻¹ * γ * (t * y) = y⁻¹ * (t⁻¹ * (γ * t)) * y := by group
      simp only [this, ← mem_cent.1 ht, inv_mul_cancel_left]
    have hF : ∀ g : Γ, AEMeasurable (fun x : H => α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)))
        (μ.restrict 𝓕) := fun g =>
      ((hαm.mul hψ).comp (measurable_const_mul (g : H))).aemeasurable
    calc ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ
        = ∫⁻ x in 𝓕, ∑' g : Γ, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) ∂μ :=
          lintegral_congr fun x => GlobalTheory.T.tsum_subgroupConjugacyClass_eq_tsum_weighted H Γ γ hγ α hα1 G x
      _ = ∑' g : Γ, ∫⁻ x in 𝓕, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) ∂μ :=
          lintegral_tsum hF
      _ = ∫⁻ y, α y * G (y⁻¹ * γ * y) ∂μ :=
          (h𝓕.lintegral_eq_tsum'' (fun y => α y * G (y⁻¹ * γ * y))).symm
      _ = dt 𝓣 * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂(quotMeas (cent γ) dt μ) :=
          hαI _ hψ hinv
  exact GlobalTheory.T.classTerm_converges_of_lintegral_unfolding_eq H Γ γ hγ μ 𝓕 (quotMeas (cent γ) dt μ) (dt 𝓣) hfin hL f c hf hfc hO.1 hO.2

end GlobalTheory.ClassUnfold
