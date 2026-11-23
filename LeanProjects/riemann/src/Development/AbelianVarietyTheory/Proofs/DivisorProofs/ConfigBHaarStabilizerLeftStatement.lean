import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBHaarStabilizerLeft
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_B_haar_stabilizer_left : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
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
  first | exact @GlobalTheory.ConeSmallClaim.unfold_claim | exact GlobalTheory.ConeSmallClaim.unfold_claim | (intros; apply GlobalTheory.ConeSmallClaim.unfold_claim <;> assumption)
