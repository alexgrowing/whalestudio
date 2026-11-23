import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOfSegRep2
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.LUnlinkedIrrOfHeredity
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductRepresentationReorderEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands Matrix

namespace UpperTheory.Lit.Dz

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem multi_irr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ)
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (multiProd (Equiv.sigmaUnique (Fin m) fun _ => Fin 1) fun _ : Fin m => detRep (Fin 1) χ).IsIrreducible := by
  have hd : ∑ j : Fin m, ((fun _ : Fin m => IrrGL.ofChar χ hχ) j).1 = m := by simp [IrrGL.ofChar]
  have hP : (prodIrr (fun _ : Fin m => IrrGL.ofChar χ hχ) hd).IsIrreducible :=
    GlobalTheory.RgGu.Unl.lUnlinkedIrr_nu k (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
      PositivityTheory.RgGu.segmentRepresentation) PositivityTheory.Geo.geometricLemmaFiltration (GlobalTheory.RgGu.Nup2.nuPair k) m m
      (fun _ => Segment.single _ (IrrGL.isCusp_ofChar _ hχ)) _ hd (fun _ _ => Segment.not_linked_self _)
      (fun _ => (single_spec (IrrGL.isCusp_ofChar _ hχ)).2.1)
  let φ := multiProdEquiv (Equiv.sigmaUnique (Fin m) fun _ => Fin 1)
    (fun _ : Fin m => GlobalTheory.LocGL.equivRep (IrrRep.det (Fin 1) χ hχ))
  obtain ⟨θ⟩ := GlobalTheory.T.product_representation_reorder_equiv k m m (fun _ => 1) (Equiv.sigmaUnique (Fin m) fun _ => Fin 1)
    (stdBlocks (fun _ : Fin m => 1) hd) _ (fun _ : Fin m => (IrrGL.ofChar χ hχ).rep)
  exact (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv φ).2
    ((GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_equiv θ).2 hP)

end UpperTheory.Lit.Dz
