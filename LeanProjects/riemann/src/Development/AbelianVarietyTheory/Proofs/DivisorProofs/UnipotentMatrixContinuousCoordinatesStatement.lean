import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMatrixContinuousCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_matrix_continuous_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∃ Ψ : (Fin d₁ → AE F E) × AE F E → Matrix (Fin d) (Fin d) (AE F E), Continuous Ψ ∧ ∀ u ∈ unip σ W H', mat u = Ψ (coA σ W.J H' u, coC σ W.J H' u) := by
  first | exact @GlobalTheory.ThK.UnipDom.matEq | exact GlobalTheory.ThK.UnipDom.matEq | (intros; apply GlobalTheory.ThK.UnipDom.matEq <;> assumption)
