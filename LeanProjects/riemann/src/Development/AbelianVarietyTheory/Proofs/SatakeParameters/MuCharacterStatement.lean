import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacter
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu_character : MuChar := by
  first | exact @GlobalTheory.MuCharProof.muChar_holds | exact GlobalTheory.MuCharProof.muChar_holds | (intros; apply GlobalTheory.MuCharProof.muChar_holds <;> assumption)
