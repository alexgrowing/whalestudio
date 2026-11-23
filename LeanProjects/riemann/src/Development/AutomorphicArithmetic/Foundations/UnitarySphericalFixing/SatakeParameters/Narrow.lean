import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem Old.typeS (s : Sw) (_H : IsRec h rc) : TypeLaw h rc := s.elim

theorem New.typeS (_s : TrivialCondition) (H : IsRecT h rc) : TypeLaw h rc := H.choose_spec.choose_spec.type

theorem narrowBig (s : Sw) (_art : GlobalTheory.Published.GlobalArtinReciprocity) (_hL : GlobalTheory.Published.LocalLanglandsGL) :
    DiscreteGroups.sglob.DzType.NarrowBig :=
  fun _ E' _ _ _ _ _ _ _ _ _ _ _ _ _ g _ _ _ _ w' h' _ H i hi n hn _ h1 h2 a' ha' K _ _ red h3 h4 θ hθ τ hτ h5 σ h6 =>
    (Old.typeS s H E' g w' h' i hi n hn h1 h2 a' ha' K red h3 h4 θ hθ τ hτ h5 σ h6).2

end UpperTheory.One.M
