import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCoordsFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_coords_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ (g : UA σ W.J) (a w : Fin m → AE F E) (α : AE F E), crd H g = Heisenberg₂ a w α →
      (∀ k, a k = -∑ j, inclR (F := F) (AF F) (W₁.J k j) * cA σ (w j)) ∧
      cA σ (2 * α + ∑ j, ∑ k, w j * inclR (F := F) (AF F) (W₁.J j k) * cA σ (w k)) =
        2 * α + ∑ j, ∑ k, w j * inclR (F := F) (AF F) (W₁.J j k) * cA σ (w k) := by
  first | exact @GlobalTheory.QhtUnip.heis_rel | exact GlobalTheory.QhtUnip.heis_rel | (intros; apply GlobalTheory.QhtUnip.heis_rel <;> assumption)
