import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalCompatibility
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_compatibility : ∀ D : D7, SumRepresentations.AdmA D → LGC D := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.local_global_compat_of_adm | exact GlobalTheory.StringRepresentationDecomposition.local_global_compat_of_adm | (intros; apply GlobalTheory.StringRepresentationDecomposition.local_global_compat_of_adm <;> assumption)
