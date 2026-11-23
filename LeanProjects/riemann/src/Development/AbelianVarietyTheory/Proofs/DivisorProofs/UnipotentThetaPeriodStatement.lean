import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentThetaPeriod
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_theta_period : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ g : UA σ G.W.J, ∃ (N : ℕ) (Λ : Fin N → (((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ)) (ψ : Fin N → ((Fin a' × Fin (a + a') → Fv F v) → ℂ)), (∀ j, ψ j ∈ SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ j, ∀ z ∈ augAt om' v, Λ j z = 0) ∧ (∀ j, ∀ n ∈ unip σ G.W H', n ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, n)) φ φ₁ → Λ j φ₁ = Λ j φ) ∧ ∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → ∃ ψ₁ : Fin N → ((Fin a' × Fin (a + a') → Fv F v) → ℂ), (∀ j, ψ₁ j ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om' (1, m)) (ψ j) (ψ₁ j)) ∧ GlobalTheory.CtTyp.ctf H' μ 𝓕 (G.M'.I om' Φ') (m * g) = ∑ j, Λ j (ψ₁ j) := by
  first | exact @GlobalTheory.FacSmall.fac | exact GlobalTheory.FacSmall.fac | (intros; apply GlobalTheory.FacSmall.fac <;> assumption)
