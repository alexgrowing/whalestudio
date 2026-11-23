import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DepthZeroEigenSpanAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalLanglandsPlaceDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaPolynomialCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeriesLocationOfMembershipStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypePrimesFinished

theorem main : GlobalTheory.HeightCounting.HtCard → PrN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => (PairedCharacterCondition.tieChi (D := w.D Z) ∧ (∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (w.D Z) ∧ GlobalTheory.TypeLeaf.SerLoc (w.D Z)) := by
  intro hC hP hW hS hL
  refine GlobalTheory.HeightCounting.Up.Model.AtMem.imp
    (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.T.depth_zero_eigen_span_admissible hC hP hW hS hL)
      (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.T.exists_local_langlands_place_datum hP hL) (GlobalTheory.T.series_location_of_membership hP hL))) ?_
  intro K B f T w Z Wt p0 t nch n c h
  obtain ⟨⟨h1, h2⟩, ⟨P, _⟩, h4⟩ := h
  exact ⟨h1, h2, GlobalTheory.T.inertia_polynomial_compatible hL (w.D Z) P, h4⟩

end GlobalTheory.TypePrimesFinished
