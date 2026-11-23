import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevel
import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), ∃ T : Finset (Formalism.AUTREP.GAf L n), ∀ g : Formalism.AUTREP.GAf L n, ∃ (γ : ReciprocityTheory.Aut.GQ L n) (t : Formalism.AUTREP.GAf L n) (u : Formalism.AUTREP.GAf L n), t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax L n ∧ g = (γ : Formalism.AUTREP.GAf L n) * t * u := by
  first | exact @GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax | exact GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax | (intros; apply GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax <;> assumption)
