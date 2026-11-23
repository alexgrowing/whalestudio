import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_add_star_eq_one_of_isCMUnram' : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∃ t : 𝓞 K, (t : K) + star (t : K) = 1 := by
  first | exact @GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram | exact GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram | (intros; apply GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram <;> assumption)
