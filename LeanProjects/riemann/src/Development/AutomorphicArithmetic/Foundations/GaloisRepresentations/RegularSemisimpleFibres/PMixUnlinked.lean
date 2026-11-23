import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.UnlType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.mixUnlinked : MixType → MixUnlinked := by
  intro hT E Ω _ _ _ _ _ _ n hn π Y hY A v w h h' g _ i hi hI τ τ' hτ hτ' hM f hf hs s hS
  obtain ⟨c, d, hd, θ, hpos, hθ, hv⟩ := hT E Ω n hn π Y hY A v w h h' g i hi hI τ τ' hτ hτ' hM f hf hs
  haveI : CharZero (w.adicCompletion Y.K) :=
    charZero_of_injective_algebraMap (algebraMap Y.K _).injective
  exact UpperTheory.Gal.TypesAndIwahori.unlinked_of_typeVec _ n c d hd hpos _ τ'.ρ τ'.smooth τ'.irred
    (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp Y.K n Y.π w τ' hτ') θ hθ hv s hS
