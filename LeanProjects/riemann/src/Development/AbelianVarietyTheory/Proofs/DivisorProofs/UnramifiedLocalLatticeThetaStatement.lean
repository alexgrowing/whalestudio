import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedLocalLatticeTheta
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_local_lattice_theta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ Λ : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ z ∈ augAt om' v, Λ z = 0) → (∀ n ∈ unip σ G.W H', n ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, n)) φ φ₁ → Λ φ₁ = Λ φ) → ∀ ψ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ p q : ℂ, ∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → ∀ ψ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, m)) ψ ψ₁ → Λ ψ₁ = p * ((GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) + q * ((GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.JacBlock₂.jacquet_position_coeff | exact GlobalTheory.JacBlock₂.jacquet_position_coeff | (intros; apply GlobalTheory.JacBlock₂.jacquet_position_coeff <;> assumption)
