import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CtfRatNormaliser
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_unipotent_integral_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ f : UA σ G.W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ G.W.J, ∀ h, f (γ * h) = f h) → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ γ ∈ ratU σ G.W.J, (∀ u ∈ unip σ G.W H', γ * u * γ⁻¹ ∈ unip σ G.W H' ∧ γ⁻¹ * u * γ ∈ unip σ G.W H') → ∀ g, GlobalTheory.CtTyp.ctf H' μ 𝓕 f (γ * g) = GlobalTheory.CtTyp.ctf H' μ 𝓕 f g := by
  first | exact @GlobalTheory.CtTyp.ctf_rat_normaliser | exact GlobalTheory.CtTyp.ctf_rat_normaliser | (intros; apply GlobalTheory.CtTyp.ctf_rat_normaliser <;> assumption)
