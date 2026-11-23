import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsCuspidal
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_reps_cuspidal : ∀ D : D7, SumRepresentations.adm2 D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  first | exact @GlobalTheory.GaloisFromAdm.main | exact GlobalTheory.GaloisFromAdm.main | (intros; apply GlobalTheory.GaloisFromAdm.main <;> assumption)
