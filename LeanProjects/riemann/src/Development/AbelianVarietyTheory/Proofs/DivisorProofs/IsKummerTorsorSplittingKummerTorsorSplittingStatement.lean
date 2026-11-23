import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplitting
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting : ∀ (q : ℕ) [NeZero q], IsKum q (kumT q) := by
  first
  | exact @GlobalTheory.EtC.KummerSplit.isKum_kumT
  | exact GlobalTheory.EtC.KummerSplit.isKum_kumT
  | (intros; apply GlobalTheory.EtC.KummerSplit.isKum_kumT <;> assumption)
