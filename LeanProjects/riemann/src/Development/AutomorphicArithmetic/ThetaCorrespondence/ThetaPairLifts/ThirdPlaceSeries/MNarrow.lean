import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Narrow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzMatchCut
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}
theorem narrowBig_alt (s : _root_.UpperTheory.One.M.TrivialCondition) (_art : GlobalTheory.Published.GlobalArtinReciprocity) (_hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.DiscreteGroups.sglob.DzType.NarrowBigAlt :=
  fun _ E' _ _ _ _ _ _ _ _ _ _ _ _ _ g _ _ _ _ w' h' _ H i hi n hn _ h1 h2 a' ha' K _ _ red h3 h4 θ hθ τ hτ h5 σ h6 =>
    (_root_.UpperTheory.One.M.New.typeS s H E' g w' h' i hi n hn h1 h2 a' ha' K red h3 h4 θ hθ τ hτ h5 σ h6).2
end UpperTheory.One.M
end
end
