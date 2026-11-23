import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoRes
import Development.DiscreteGroups.GlobalIrreducibility.DzGalW
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.baseQ :
    CardRes → BaseQ := by
  intro _ E _ _ v g _ i hi
  have e : 𝓀[v.adicCompletion E] ≃+* ZMod g :=
    (Ideal.quotEquivOfEq (DiscreteGroups.sglob.DzIso.ker_redO i hi).symm).trans
      (RingHom.quotientKerEquivOfSurjective (DiscreteGroups.sglob.DzIso.redO_surjective i hi))
  exact ⟨DiscreteGroups.sglob.DzType.g_not_mem_sq v g i hi, by rw [Nat.card_congr e.toEquiv, Nat.card_zmod], ⟨e⟩⟩
