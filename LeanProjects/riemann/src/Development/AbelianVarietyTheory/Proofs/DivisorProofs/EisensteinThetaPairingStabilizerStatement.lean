import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinThetaPairingStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_theta_pairing_stabilizer : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om', IsTriple B G X om om' → ∀ K : Subgroup (UA σ G.V'.J), IsStab B K →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Eis : ℂ → UA σ G.V'.J → ℂ, GlobalTheory.ConeSmall.IsEisSer K H.x Eis →
    GlobalTheory.ConeSmallCT.EisGood b Eis → ∀ (μ₁ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ₁.IsHaarMeasure →
    IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ₁ → μ₁ 𝓕 = 1 → ∀ h,
      (∀ s₀ : ℂ, MeromorphicAt (fun s => ∫ u in 𝓕, GlobalTheory.ConeSmallCT.Bint G.M' om' Φ' Eis s (u.1 * h) ∂μ₁) s₀) ∧
      AnalyticAt ℂ (fun s => ∫ u in 𝓕, GlobalTheory.ConeSmallCT.Bint G.M' om' Φ' Eis s (u.1 * h) ∂μ₁) (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) := by
  first | exact @GlobalTheory.ConeSmallMero.ct_mero | exact GlobalTheory.ConeSmallMero.ct_mero | (intros; apply GlobalTheory.ConeSmallMero.ct_mero <;> assumption)
