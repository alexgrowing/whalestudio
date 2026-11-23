import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.FieldGT

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.One.M.New.field {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}
    (_hL : RecTExists) {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    {rc' : IrrGL (w'.adicCompletion E') → WD h'} (H : IsRecT h rc) (H' : IsRecT h' rc') : UpperTheory.One.M.FieldG rc rc' :=
  UpperTheory.One.M.fieldGT E Ω A w h E' Ω' A' w' h' rc rc' H H'
