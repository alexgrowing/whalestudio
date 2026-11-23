import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermFundamentalDomain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_fundamental_domain : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → (∀ Φ ∈ PolData B G.M, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, ∃ (N K : ℕ) (χ : Fin N → (AE F E)ˣ →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ ∧ ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m → ∫ u in 𝓕, G.M.I om Φ (u.1 * (m * h)) ∂μ = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) ^ (k : ℕ)) ∧ ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, ∃ (N K : ℕ) (χ : Fin N → (AE F E)ˣ →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ ∧ ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m → ∫ u in 𝓕, G.M'.I om' Φ' (u.1 * (m * h)) ∂μ = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) ^ (k : ℕ) := by
  first | exact @GlobalTheory.ThKCtFin.ctFin | exact GlobalTheory.ThKCtFin.ctFin | (intros; apply GlobalTheory.ThKCtFin.ctFin <;> assumption)
