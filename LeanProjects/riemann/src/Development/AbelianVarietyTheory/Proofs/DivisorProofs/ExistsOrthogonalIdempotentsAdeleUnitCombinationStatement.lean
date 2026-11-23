import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentsAdeleUnitCombination
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (n u : ι → AF F), IsUnit (∑ i, u i * n i) → ∃ η : ι → AF F, (∀ i, η i * η i = η i) ∧ (∀ i j, i ≠ j → η i * η j = 0) ∧ ∑ i, η i = 1 ∧ IsUnit (∑ i, η i * n i) := by
  first | exact @GlobalTheory.QSA.exists_idem_pick_unit | exact GlobalTheory.QSA.exists_idem_pick_unit | (intros; apply GlobalTheory.QSA.exists_idem_pick_unit <;> assumption)
