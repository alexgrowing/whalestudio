import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveEtaleCohomologicalDimensionLeOn
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one : GlobalTheory.EtC.C2 := by
  first | (exact @GlobalTheory.EtC.etC_c2) | (exact GlobalTheory.EtC.etC_c2) | (intros; apply GlobalTheory.EtC.etC_c2  <;> assumption)
