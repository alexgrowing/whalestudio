import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedDataIntegralIdentity
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
theorem _root_.GlobalTheory.T.polarized_data_integral_identity : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ K : Subgroup (UA σ G.V'.J), IsStab B K → ∀ X om om', IsTriple B G X om om' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∀ hf : UA σ G.V'.J → ℝ, GlobalTheory.ConeSmall.IsIwaHt K H.x hf → (∀ g, ∃ (p k : UA σ G.V'.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k) →
    ∀ Eis : ℂ → UA σ G.V'.J → ℂ, GlobalTheory.ConeSmall.IsEisSer K H.x Eis →
    ∃ 𝓓 : Set (UA σ G.V'.J), IsFundamentalDomain (ratStab σ G.V'.J H.x) 𝓓 G.M'.μ ∧ ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re → ∀ h,
      GlobalTheory.ConeSmallCT.Bint G.M' om' Φ' Eis s h = ∫ g in 𝓓, theta om' Φ' g h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2) ∂G.M'.μ ∧
      IntegrableOn (fun g => theta om' Φ' g h * (hf g : ℂ) ^ (s + (((b + 2 : ℕ) : ℂ) - 1) / 2)) 𝓓 G.M'.μ := by
  first | exact @GlobalTheory.ConeSmallUnfEis.unfold_eis | exact GlobalTheory.ConeSmallUnfEis.unfold_eis | (intros; apply GlobalTheory.ConeSmallUnfEis.unfold_eis <;> assumption)
