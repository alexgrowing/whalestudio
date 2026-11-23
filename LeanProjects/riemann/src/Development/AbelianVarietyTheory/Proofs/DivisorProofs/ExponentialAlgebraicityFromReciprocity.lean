import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRootOfExp
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleRootOfPrintStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSeriesOfReciprocityHypothesesStatement

set_option autoImplicit false
noncomputable section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

theorem expAlg : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → ExpAlg := fun h1 h2 h3 h4 =>
  expAlg_of_serAlg (serAlg_of_ref (GlobalTheory.T.rational_series_of_reciprocity_hypotheses h1 h2 h3 h4) (GlobalTheory.T.scaleRoot_of_cuspRapidDecay_of_reciprocity_of_rayClassField h1 h2 h3 h4))

end GlobalTheory.BigOn.Exp
