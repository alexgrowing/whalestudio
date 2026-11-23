import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSheafIsLocallyFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistSheaf_isLocallyFlat : ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i) := by
  first | (exact @GlobalTheory.EtC.flatS_tw) | (exact GlobalTheory.EtC.flatS_tw) | (intros; apply GlobalTheory.EtC.flatS_tw  <;> assumption)
