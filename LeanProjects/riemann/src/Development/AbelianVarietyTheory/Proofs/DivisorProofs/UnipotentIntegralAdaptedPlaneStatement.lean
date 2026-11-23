import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentIntegralAdaptedPlane
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_integral_adapted_plane : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ Φ ∈ PolData B G.M, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ (v : Pl F) (g : UA σ G.W.J), ∃ (n : ℕ) (ψ : Fin n → (Fin a × Fin (a + a') → Fv F v) → ℂ) (ℓ : Fin n → ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ), (∀ j, ψ j ∈ SB (Fin a × Fin (a + a') → Fv F v)) ∧ (∀ j, augAt om v ≤ LinearMap.ker (ℓ j)) ∧ (∀ j, ∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, u)) φ φ₁ → ℓ j φ₁ = ℓ j φ) ∧ ∀ m ∈ UAt σ G.W (evFin F v), ∃ ψ₁ : Fin n → (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ j, ψ₁ j ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om (1, m)) (ψ j) (ψ₁ j)) ∧ GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M.I om Φ) (m * g) = ∑ j, ℓ j (ψ₁ j) := by
  first | exact @GlobalTheory.CtLocFac.fac | exact GlobalTheory.CtLocFac.fac | (intros; apply GlobalTheory.CtLocFac.fac <;> assumption)
