import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIsoIsometryCubical
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_iso_isometry_cubical : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (r : E → ℂ), IsFactor B τ (stdLat g) j → (∃ ι, IsBundleIso B τ (stdLat g) (mulPullFactor (-1) j) j ι) → IsRigidification B r → InducesPolarisation B τ (stdLat g) j → ∀ n : ℤ, ∀ h φ, IsCubicalMetric B τ j r h → IsSquareIso B τ j r n φ → IsIsometry B (fun P => h (mulN n P)) (fun P => h P ^ (n.natAbs ^ 2)) φ := by
  first | exact @GlobalTheory.SqIsoIsom.sqIso_isometry | exact GlobalTheory.SqIsoIsom.sqIso_isometry | (intros; apply GlobalTheory.SqIsoIsom.sqIso_isometry <;> assumption)
