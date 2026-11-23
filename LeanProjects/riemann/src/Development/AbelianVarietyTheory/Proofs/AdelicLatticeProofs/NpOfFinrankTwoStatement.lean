import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfFinrankTwo
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.np_of_finrank_two' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → NP F E := by
  first | exact @GlobalTheory.CNorm.np_of_finrank_two | exact GlobalTheory.CNorm.np_of_finrank_two | (intros; apply GlobalTheory.CNorm.np_of_finrank_two <;> assumption)
