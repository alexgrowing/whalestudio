import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.P

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem toTL (N : GlobalTheory.Mem.LiteralAutomorphy.LitN) (k : IsRec h rc) : IsRecT h rc := isRecT_of_isRec N.loc.dzt k

theorem toTL' (_N : GlobalTheory.Mem.LiteralAutomorphy.LitN) (k : IsRecT h rc) : IsRecT h rc := k

end UpperTheory.V.Z.Desc.P
