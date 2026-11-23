import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleChartSmoothAlgebraLocalPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_chart_smooth_algebra_local_point : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A] [Algebra.Smooth R A] (ε : A →ₐ[R] R), ∃ (g : ℕ) (t : Fin g → A) (h : A), (∀ i, ε (t i) = 0) ∧ IsUnit (ε h) ∧ GlobalTheory.DenseSec.EtChart R A t h := by
  first | exact @GlobalTheory.DenseSec.exists_etChart | exact GlobalTheory.DenseSec.exists_etChart | (intros; apply GlobalTheory.DenseSec.exists_etChart <;> assumption)
