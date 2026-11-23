import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_unit_split_place_conjugate_prime : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L), ∃ e : 𝓞 L, Valued.v (s.i (e : L)) = 1 ∧ Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 := by
  first | exact @GlobalTheory.SplitSep.exists_sep | exact GlobalTheory.SplitSep.exists_sep | (intros; apply GlobalTheory.SplitSep.exists_sep <;> assumption)
