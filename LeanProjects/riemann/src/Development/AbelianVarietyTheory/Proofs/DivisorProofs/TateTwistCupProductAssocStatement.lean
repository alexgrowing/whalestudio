import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssoc
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCupProduct_assoc : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l), cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring) := by
  first
  | exact @GlobalTheory.EtC.CupAssoc.main
  | exact GlobalTheory.EtC.CupAssoc.main
  | (intros; apply GlobalTheory.EtC.CupAssoc.main <;> assumption)
