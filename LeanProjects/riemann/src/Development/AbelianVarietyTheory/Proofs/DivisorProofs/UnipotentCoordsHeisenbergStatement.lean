import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordsHeisenberg
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_coords_heisenberg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ u ∈ unip σ W H, ∃ (a w : Fin m → AE F E) (α : AE F E), crd H u = Heisenberg₂ a w α := by
  first | exact @GlobalTheory.QhtUnip.crd_unip_eq_heis | exact GlobalTheory.QhtUnip.crd_unip_eq_heis | (intros; apply GlobalTheory.QhtUnip.crd_unip_eq_heis <;> assumption)
