import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFixLeRatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarNormalizedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarGlobalFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarVolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarConvergence
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.ConeSmallClaim

theorem unfold_claim : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ γ, IsWitt (σ := σ) (J := G.W.J) H'.x γ →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∀ hf : UA σ G.V'.J → ℝ, GlobalTheory.ConeSmall.IsIwaHt K H.x hf → (∀ g, ∃ (p k : UA σ G.V'.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k) →
    ∀ 𝓓 : Set (UA σ G.V'.J), IsFundamentalDomain (ratStab σ G.V'.J H.x) 𝓓 G.M'.μ →
    ∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → (∀ h, (∀ w, IntegrableOn (fun g => ‖termW B G.M' H H' e' om' Φ' γ w g h‖ * hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2)) 𝓓 G.M'.μ) ∧
        Summable fun w => ∫ g in 𝓓, ‖termW B G.M' H H' e' om' Φ' γ w g h‖ * hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2) ∂G.M'.μ) ∧
      ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x →
        GlobalTheory.ConeSmallCT.LocUnifSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) T := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ hf hhf hIw 𝓓 h𝓓
  have hnn0 : ∀ g, 0 ≤ hf g := fun g => by
    obtain ⟨p, k, l, hk, hp, rfl⟩ := hIw g
    rw [hhf p k l hk hp]; exact NNReal.coe_nonneg _
  obtain ⟨s₁, hE⟩ := GlobalTheory.T.seesaw_evaluation_haar_global_factor hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ hf hhf hIw
  refine ⟨s₁, fun s hs => ⟨fun h => ?_, fun T hTr => ?_⟩⟩
  · obtain ⟨𝓓₁, R, h𝓓₁, hR, hle⟩ := GlobalTheory.T.seesaw_evaluation_haar_volume hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ hf hhf hIw 𝓓 h𝓓
    obtain ⟨A, hA, hAb⟩ := hE s.re hs {h} isCompact_singleton
    have hfin : ∑' w, ∫⁻ g in 𝓓, ENNReal.ofReal (‖termW B G.M' H H' e' om' Φ' γ w g h‖ *
        hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2)) ∂G.M'.μ ≠ ⊤ :=
      ne_top_of_le_ne_top (hA R hR)
        ((hle _ h).trans (ENNReal.tsum_le_tsum fun w => hAb 𝓓₁ h𝓓₁ w.1 h (Set.mem_singleton h)))
    have hnn : ∀ w g, 0 ≤ ‖termW B G.M' H H' e' om' Φ' γ w g h‖ * hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2) :=
      fun w g => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hnn0 g) _)
    have hint : ∀ w, IntegrableOn (fun g => ‖termW B G.M' H H' e' om' Φ' γ w g h‖ *
        hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2)) 𝓓 G.M'.μ := fun w => by
      refine ⟨(GlobalTheory.T.seesaw_evaluation_haar_normalized hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ hf hhf hIw w h _).restrict, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hnn w))]
      exact lt_of_le_of_lt (ENNReal.le_tsum w) (lt_top_iff_ne_top.2 hfin)
    refine ⟨hint, ?_⟩
    have e : ∀ w, ∫ g in 𝓓, ‖termW B G.M' H H' e' om' Φ' γ w g h‖ * hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2) ∂G.M'.μ =
        (∫⁻ g in 𝓓, ENNReal.ofReal (‖termW B G.M' H H' e' om' Φ' γ w g h‖ *
          hf g ^ (s.re + (((b + 2 : ℕ) : ℝ) - 1) / 2)) ∂G.M'.μ).toReal := fun w =>
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn w)) (hint w).1
    simp_rw [e]
    exact ENNReal.summable_toReal hfin
  · intro S hS
    obtain ⟨𝓓₁, h𝓓₁, C, hC, φ, hφ, hbd⟩ := GlobalTheory.T.seesaw_evaluation_haar_convergence hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ hf hhf hIw s T hTr
    obtain ⟨A, hA, hAb⟩ := hE s.re hs S hS
    have hinj : Function.Injective φ := fun t t' e => hφ t t' 1 (by rw [e]; simp)
    have hNP : GlobalTheory.ConeSmallClaim.NonProp (Set.range φ) := by
      rintro _ ⟨t, rfl⟩ _ ⟨t', rfl⟩ ξ e
      rw [hφ t t' ξ e]
    have hsum : ∑' t, A (φ t) ≠ ⊤ := by
      have := hA _ hNP
      rwa [tsum_range (f := A) hinj] at this
    refine ⟨fun t => (C * A (φ t)).toReal,
      ENNReal.summable_toReal (by rw [ENNReal.tsum_mul_left]; exact ENNReal.mul_ne_top hC hsum), fun t h hh => ?_⟩
    have hAt : A (φ t) ≠ ⊤ := ne_top_of_le_ne_top hsum (ENNReal.le_tsum t)
    have := (hbd t h).trans (mul_le_mul_right (hAb 𝓓₁ h𝓓₁ (φ t) h hh) C)
    exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hC hAt)).1 this

end GlobalTheory.ConeSmallClaim

end
