import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrabilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainFlowIntegralIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlowDerivativeIntegralByPartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalStatementSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaLocalIntegralIdentityStatement

namespace GlobalTheory.ThKL2Der

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem tendsto_eLpNorm_difference_quotient_sub (μ : Measure H) [μ.IsHaarMeasure] (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (γ : Multiplicative ℝ →* H) (hγ : Continuous γ)
    (f f₁ : H → ℂ) (hder : ∀ x, HasDerivAt (fun t : ℝ => f (x * γ (Multiplicative.ofAdd t))) (f₁ x) 0)
    (hc : Continuous f₁) (hinv : ∀ g ∈ Γ, ∀ x, f₁ (g * x) = f₁ x)
    (hsq : IntegrableOn (fun x => ‖f₁ x‖ ^ 2) 𝓕 μ) :
    Tendsto (fun t : ℝ => eLpNorm (fun x => (t : ℂ)⁻¹ * (f (x * γ (Multiplicative.ofAdd t)) - f x) - f₁ x) 2
      (μ.restrict 𝓕)) (𝓝[≠] 0) (𝓝 0) := by
  set N : ℝ → ENNReal := fun s => eLpNorm (fun x => f₁ (x * γ (Multiplicative.ofAdd s)) - f₁ x) 2 (μ.restrict 𝓕)
  have hN : Tendsto N (𝓝 0) (𝓝 0) := GlobalTheory.T.fundamental_domain_flow_integral_identity μ Γ 𝓕 h𝓕 γ hγ f₁ hc hinv hsq
  have hS : Tendsto (fun t : ℝ => ⨆ s ∈ Set.uIcc 0 t, N s) (𝓝[≠] 0) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have h1 := (ENNReal.tendsto_nhds_zero.1 hN) ε hε
    obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1 h1
    refine eventually_nhdsWithin_of_eventually_nhds (Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun t ht => ?_⟩)
    refine iSup₂_le fun s hs => hδs ?_
    have hst : |s| ≤ |t| := by
      rcases Set.mem_uIcc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact abs_le_abs h2 (by linarith)
      · exact (abs_le_abs (show s ≤ -t by linarith) (by linarith)).trans_eq (abs_neg t)
    rw [Real.dist_eq, sub_zero] at ht ⊢
    exact lt_of_le_of_lt hst ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hS (Eventually.of_forall fun _ => zero_le') ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact GlobalTheory.T.flow_derivative_integral_by_parts μ 𝓕 γ hγ f f₁ hder hc t ht

theorem theta_l2_derivative : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (μ : MeasureTheory.Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (𝓕 : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), μ.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ G.W.J) 𝓕 μ → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Φ₁ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Filter.Tendsto (fun t : ℝ => MeasureTheory.eLpNorm (fun x => (t : ℂ)⁻¹ * (G.M'.I om' Φ (x * γ (Multiplicative.ofAdd t)) - G.M'.I om' Φ x) - G.M'.I om' Φ₁ x) 2 (μ.restrict 𝓕)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 γ hγ Φ hΦ Φ₁ hΦ₁ hd
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (a + a') G.W.J
  haveI := i1; haveI := i2; haveI := i3; haveI := i4
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI := hμ
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ G.W.J
  have hsq := (GlobalTheory.T.square_integrability hKP F E σ B a a' G X om om' hM.triple μ 𝓕 hμ h𝓕).2 Φ₁ hΦ₁
  exact tendsto_eLpNorm_difference_quotient_sub μ (ratU σ G.W.J) 𝓕 h𝓕 γ hγ.1 (G.M'.I om' Φ) (G.M'.I om' Φ₁)
    (GlobalTheory.T.matched_triple_global_statement hKP F E σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hΦ₁ hd)
    (GlobalTheory.T.matched_triple_global_statement_second hKP F E σ B a a' G X om om' R Rf hM Φ₁ hΦ₁)
    (GlobalTheory.T.matched_theta_local_integral_identity hKP F E σ B a a' G X om om' R Rf hM Φ₁ hΦ₁) hsq

end GlobalTheory.ThKL2Der
