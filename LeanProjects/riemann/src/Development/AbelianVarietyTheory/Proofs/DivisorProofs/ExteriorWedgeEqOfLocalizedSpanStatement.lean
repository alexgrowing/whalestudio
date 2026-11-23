import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorWedgeEqOfLocalizedSpan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exterior_wedge_eq_of_localized_span : ∀ (R L M : Type) [CommRing R] [Field L] [Algebra R L] [AddCommGroup M] [Module L M] (S : Submonoid R) (n : ℕ) (g w : Fin n → M), (∀ i, ∃ r ∈ S, ∃ c : Fin n → R, algebraMap R L r • w i = ∑ l, algebraMap R L (c l) • g l) → ∃ r ∈ S, ∃ c : R, algebraMap R L r • ExteriorAlgebra.ιMulti L n w = algebraMap R L c • ExteriorAlgebra.ιMulti L n g := by
  first | (exact @GlobalTheory.WedgeDen.exists_smul_ιMulti_eq_smul_ιMulti) | (exact GlobalTheory.WedgeDen.exists_smul_ιMulti_eq_smul_ιMulti) | (intros; apply GlobalTheory.WedgeDen.exists_smul_ιMulti_eq_smul_ιMulti  <;> assumption)
