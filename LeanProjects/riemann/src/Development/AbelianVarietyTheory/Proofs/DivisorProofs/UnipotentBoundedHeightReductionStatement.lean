import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBoundedHeightReduction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_bounded_height_reduction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∃ R : ℝ≥0, ∀ u ∈ unip σ W H', ∃ γ ∈ ratU σ W.J ⊓ unip σ W H', ht (γ * u) ≤ R := by
  first | exact @GlobalTheory.UnipCompact.exists_bounded_translate | exact GlobalTheory.UnipCompact.exists_bounded_translate | (intros; apply GlobalTheory.UnipCompact.exists_bounded_translate <;> assumption)
