import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubquotientOfProductOfSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairIrreducibleUnlinked
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfExtTensor
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.unlFull :
    UnlFull := by
  intro k _ _ _ _ _ N V _ _ π s x hd hs hu
  have hmem : ∀ a, x a ∈ Finset.univ.val.map x := fun a =>
    Multiset.mem_map_of_mem x (Finset.mem_univ_val a)
  have hx : ∀ a, (x a).IsCusp := fun a => hs.isCusp (hmem a)
  have hP : (prodIrr x hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k s N (fun a => Segment.single (x a) (hx a)) x hd
      (fun a b => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hx a) (hx b) (hu _ (hmem b) _ (hmem a))
        (hu _ (hmem a) _ (hmem b)))
      (fun a => (single_spec (hx a)).2.1)
  have h1 := GlobalTheory.LocGL.SupportPerm.isSubquotient_prodIrr_of_hasSupport
    UpperTheory.Zero.LLC.Pr.zel UpperTheory.Zero.LLC.Pr.bz k N s ⟨V, π, hs.isSmooth, hs.isIrreducible⟩ x hd hs
  haveI := GlobalTheory.ReducedFactor.nontrivial_of_irr hs.isIrreducible
  obtain ⟨E⟩ := GlobalTheory.TypeTwo.PowIrrProof.equiv_of_isSubquotient h1 hP
  exact ⟨E.symm⟩
