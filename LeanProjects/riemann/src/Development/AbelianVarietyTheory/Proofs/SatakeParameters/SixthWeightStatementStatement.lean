import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sixth_weight_statement : PurityStringWeight := by
  first | exact @GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity | exact GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity | (intros; apply GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity <;> assumption)
