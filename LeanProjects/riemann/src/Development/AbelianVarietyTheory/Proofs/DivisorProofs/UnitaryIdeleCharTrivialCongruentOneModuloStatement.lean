import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIdeleCharTrivialCongruentOneModulo
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocF
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryIdeleChar_trivial_congruentOneModulo : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : (AF F ⊗[F] E)ˣ →* Circle), Continuous ν → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitGen.modSetF F E N, ν x = 1 := by
  first | exact @GlobalTheory.HeckeSplitGen.char_trivial_modSetF | exact GlobalTheory.HeckeSplitGen.char_trivial_modSetF | (intros; apply GlobalTheory.HeckeSplitGen.char_trivial_modSetF <;> assumption)
