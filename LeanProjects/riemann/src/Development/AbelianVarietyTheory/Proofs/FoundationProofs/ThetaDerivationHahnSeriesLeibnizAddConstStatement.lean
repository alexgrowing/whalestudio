import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaDerivationHahnSeriesLeibnizAddConst
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (P Q : HahnSeries ℚ Ω), theta s (P * Q) = theta s P * Q + P * theta s Q ∧ theta s (P + Q) = theta s P + theta s Q ∧ ∀ c : Ω, theta s (HahnSeries.C c) = 0 := by
  first | exact @GlobalTheory.Glue.theta_leibniz_add_const | exact GlobalTheory.Glue.theta_leibniz_add_const | (intros; apply GlobalTheory.Glue.theta_leibniz_add_const <;> assumption)
