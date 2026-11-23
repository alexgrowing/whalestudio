import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceOfLefschetzAndGroupSide
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.DefiniteTraceForms.WeightedCountDefiniteUnitary

namespace UpperTheory.Gal.LocalSmoothExtension

theorem ksHodge_of_geo (hW : HolomorphicLefschetzFormula) (hF : FixK) : UpperTheory.Gal.Int.Geo.KSHodge :=
  ksHodge_of_inputs hW hF UpperTheory.Gal.Cnt.weighted_count_definite_unitary UpperTheory.Gal.Cnt.trace_definite_forms_identity

end UpperTheory.Gal.LocalSmoothExtension
