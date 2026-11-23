import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfPublishedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LlOf
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recTExists_of_published_inputs : _root_.UpperTheory.Zero.LLC.RecTExists → LocalConverseGL → DepthZeroInduction → BrauerDegreeZero → ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → _root_.UpperTheory.Zero.LLC.RecTExists := by
  first | exact @_root_.UpperTheory.One.M.New.llOf_alt | exact _root_.UpperTheory.One.M.New.llOf_alt | (intros; apply _root_.UpperTheory.One.M.New.llOf_alt <;> assumption)
end
