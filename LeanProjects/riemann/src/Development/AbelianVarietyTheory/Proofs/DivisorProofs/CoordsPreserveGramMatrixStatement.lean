import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsPreserveGramMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_preserve_gram_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ g : UA σ W.J, (crd H g)ᵀ * (gI W₁.J).map (inclR (F := F) (AF F)) * (crd H g).map (cA σ) =
      (gI W₁.J).map (inclR (F := F) (AF F)) := by
  first | exact @GlobalTheory.QhtUnip.unit_crd | exact GlobalTheory.QhtUnip.unit_crd | (intros; apply GlobalTheory.QhtUnip.unit_crd <;> assumption)
