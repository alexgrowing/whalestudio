import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneLocalVectorInvariance
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_local_vector_invariance : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ ℓ : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, augAt om v ≤ LinearMap.ker ℓ → (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, u)) φ₀ φ₁ → ℓ φ₁ = ℓ φ₀) → ∃ p q : ℂ, ∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → m ∈ UAt σ G.W (evFin F v) → ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, m)) φ φ₁ → ℓ φ₁ = p * ((GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) + q * ((GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.JacquetLine.firstBlockScalar_coeff | exact GlobalTheory.JacquetLine.firstBlockScalar_coeff | (intros; apply GlobalTheory.JacquetLine.firstBlockScalar_coeff <;> assumption)
