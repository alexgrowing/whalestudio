import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubquotientOfProductOfSupport

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.suppStd :
    SuppStd := by
  intro k _ _ _ _ _ N V _ _ π S hS
  obtain ⟨t, x, hx, -⟩ := id hS
  have hsum := hS.sum_fst
  have hd : ∑ a, (x a).fst = N := by
    rw [← hx, Multiset.map_map] at hsum
    simpa [Finset.sum_eq_multiset_sum] using hsum
  let τ : IrrRep (GL (Fin N) k) := ⟨V, π, hS.isSmooth, hS.isIrreducible⟩
  refine ⟨t, x, hd, hx, ?_⟩
  exact SupportPerm.isSubquotient_prodIrr_of_hasSupport UpperTheory.Zero.LLC.Pr.zel UpperTheory.Zero.LLC.Pr.bz k N t τ x hd
    (hx ▸ hS)
