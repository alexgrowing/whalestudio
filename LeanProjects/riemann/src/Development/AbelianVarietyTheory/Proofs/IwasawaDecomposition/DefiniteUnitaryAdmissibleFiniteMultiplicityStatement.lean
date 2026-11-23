import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryAdmissibleFiniteMultiplicity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_admissible_finiteMultiplicity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n), (∀ K : Subgroup (finU E n), IsOpen (K : Set (finU E n)) → FiniteDimensional ℂ (fixed (π.rep.comp (finU E n).subtype) K)) ∧ FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) := by
  first | exact @GlobalTheory.DefU.admitted.admissible_finiteMult | exact GlobalTheory.DefU.admitted.admissible_finiteMult | (intros; apply GlobalTheory.DefU.admitted.admissible_finiteMult <;> assumption)
