import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHeightBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_height_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {d d₁ : ℕ}
    (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s → ∀ (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ h : UA σ W.J, ∃ C : ℝ, ∀ u ∈ unip σ W H', (qht (u * h) : ℝ) ≤ C := by
  first | exact @GlobalTheory.QhtUnip.qht_bdd_unip | exact GlobalTheory.QhtUnip.qht_bdd_unip | (intros; apply GlobalTheory.QhtUnip.qht_bdd_unip <;> assumption)
