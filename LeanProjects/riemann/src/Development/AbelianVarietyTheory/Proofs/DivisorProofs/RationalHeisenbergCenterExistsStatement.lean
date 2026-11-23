import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalHeisenbergCenterExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_heisenberg_center_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ f : E, σ f = f → ∃ γ ∈ ratU σ W.J, crd H γ = Heisenberg₂ 0 0 (inclR (F := F) (AF F) f) := by
  first | exact @GlobalTheory.LiftCentral.exists_rat_heis_center | exact GlobalTheory.LiftCentral.exists_rat_heis_center | (intros; apply GlobalTheory.LiftCentral.exists_rat_heis_center <;> assumption)
