import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEqAdicCompletionIntegers
import Mathlib
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_binary_quadratic_eq_unit_of_disc_isUnit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  first | exact @GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | exact GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | (intros; apply GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers <;> assumption)
