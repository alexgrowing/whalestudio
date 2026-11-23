import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.LUnlinkedIrrOfHeredity
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerHeredity.Replay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedLayersHoldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentGenericOfJacquetNuPairStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProductStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import GroundTheory.PAdicHodge.AInfGalois

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_map_fst_ms (Δ : Segment k) : (Δ.ms.map Sigma.fst).sum = Δ.deg := by
  rw [Segment.ms, Multiset.map_map, ← Δ.sum_term_fst]
  rfl

theorem unlinkedRealize_of (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hL : GlobalTheory.BZSeg.LUnlinkedIrr k)
    (hG : GlobalTheory.BZSeg.LSegGeneric k) (hP : GlobalTheory.BZMir.Leib.GenericProdIff k) : UnlinkedRealize k := by
  intro N s hs hN
  obtain ⟨h, Δ, hun, hbind⟩ := GlobalTheory.T.unlinked_layers_hold k s hs
  choose π hπ using fun i => GlobalTheory.T.exists_segment_representation hA (Δ i)
  let x : Fin h → IrrGL k := fun i => IrrGL.of (π i).ρ (π i).smooth (π i).irr
  have hx : ∀ i, IsLSeg (Δ i) (x i).rep := fun i => (hπ i).of_equiv (IrrGL.equivOf _ _ _)
  have hd : ∑ a, (x a).1 = N := by
    rw [← hN, ← hbind, Multiset.map_bind, Multiset.sum_bind]
    change ∑ a, (Δ a).deg = _
    rw [Finset.sum_eq_multiset_sum]
    congr 1
    exact Multiset.map_congr rfl fun i _ => (sum_map_fst_ms (Δ i)).symm
  have hirr : (prodIrr x hd).IsIrreducible :=
    hL h N Δ x hd (fun i j => if e : i = j then e ▸ Segment.not_linked_self _ else hun i j e) hx
  refine ⟨h, Δ, x, hd, hun, hx, ?_, ?_⟩
  · have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (t := fun i => (Δ i).ms)
      (fun i => (hx i).hasSupport) hirr (IsSubquotient.refl _)
    rwa [show (∑ i, (Δ i).ms) = s from hbind] at this
  · exact (hP h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V) (fun a => (x a).rep)
      (fun a => (x a).2.rep.smooth)).2 fun i => hG (Δ i) _ _ _ (hx i)

theorem unlinkedRealize (hJ : Zc.LSegJacquet k) (hN : GlobalTheory.BZSeg.NuPair k) : UnlinkedRealize k :=
  unlinkedRealize_of PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    (GlobalTheory.RgGu.Unl.lUnlinkedIrr_nu k hJ PositivityTheory.Geo.geometricLemmaFiltration hN)
    (GlobalTheory.T.segment_generic_of_jacquet_nu_pair k PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hJ hN)
    (GlobalTheory.T.whittaker_heredity_generic_product k (PositivityTheory.rg.gu.hered2.whitHeredity_all k))

end GlobalTheory.RgGu

end
