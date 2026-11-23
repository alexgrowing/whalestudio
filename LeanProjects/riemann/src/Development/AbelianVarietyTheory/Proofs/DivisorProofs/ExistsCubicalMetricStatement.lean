import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalMetric
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubical_metric : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (r : E → ℂ), IsFactor B τ (stdLat g) j → (∃ ι, IsBundleIso B τ (stdLat g) (mulPullFactor (-1) j) j ι) → IsRigidification B r → InducesPolarisation B τ (stdLat g) j → ∃ h, IsCubicalMetric B τ j r h := by
  first | exact @GlobalTheory.CubicalExist.exists_cubicalMetric | exact GlobalTheory.CubicalExist.exists_cubicalMetric | (intros; apply GlobalTheory.CubicalExist.exists_cubicalMetric <;> assumption)
