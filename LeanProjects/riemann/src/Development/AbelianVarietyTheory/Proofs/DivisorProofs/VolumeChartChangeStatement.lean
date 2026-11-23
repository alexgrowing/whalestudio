import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeChartChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sign_iMulti_D_chart_change : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ i : Fin (d + 1), ∃ ε : ℤˣ, (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (x (i.succAbove j) / x i))) = ε • algebraMap F K (∏ j, x j / x i) • vol0 k K x := by
  first | (exact @GlobalTheory.PD.volume_chart_change) | (exact GlobalTheory.PD.volume_chart_change) | (intros; apply GlobalTheory.PD.volume_chart_change <;> assumption)
