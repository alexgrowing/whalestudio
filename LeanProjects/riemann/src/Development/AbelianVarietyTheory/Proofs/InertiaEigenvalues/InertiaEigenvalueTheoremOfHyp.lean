import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistAllPowersOfGaloisCohomologyClassField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesRealizationOfPublishedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw

namespace GlobalTheory.ExportFirst

theorem exportF_isBuiltE : GlobalTheory.TwSys.Cheb → GlobalTheory.Published.PoitouTateTotallyComplex → GlobalTheory.Published.CohDimTwo → GlobalTheory.Published.TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → GlobalTheory.Published.RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.GalOfCusp.LocalGlobalAboveL → (∀ D : D7, LocalSituation.Conclusion5 D) → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : GlobalTheory.Mem.Top.Bl.Prm hL), (GlobalTheory.Mem.Top.EvLgG fun K B f T => GlobalTheory.Mem.Top.Bl.KPx B f → T = GlobalTheory.Mem.Top.TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (p.N K B f T w Z Wt p0 t nch n xd c) → Nonempty (p.R K B f T w Z Wt p0 t) → GlobalTheory.Mem.Top.Bl.ColPin w → Nonempty (TwOf hL K B f T w Z Wt p0 t nch n xd c)) → GlobalTheory.Mem.Top.GroupRetwisting.ExportF GlobalTheory.Mem.Top.Bl.KPx (GlobalTheory.Mem.Top.Bl.IsBuiltE p.s) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hA hG hR hLG hconds hL p H
  refine H.imp fun K _ _ _ _ hK => hK.imp fun B f T _ hp hKP hT C W V S N G c hc => ?_
  obtain ⟨w, Z, c', ⟨b, -⟩, e⟩ := hc
  suffices hs : ∀ y : Σ (C : GlobalTheory.Mem.Cols B) (Y : GlobalTheory.Mem.Col2.TC.Later B C),
      GlobalTheory.Mem.Top.V4.Core K ⟨B, C, Y.W, Y.V, Y.S, Y.N, Y.G⟩ f T, y = ⟨w.C, Z, c'⟩ →
      GlobalTheory.Mem.Top.ExportAt (GlobalTheory.Mem.assemble B y.1 y.2.1.W y.2.1.V y.2.1.S y.2.1.N y.2.1.G) y.2.2.O.nch y.2.2.O.xd from
    hs _ e
  rintro _ rfl
  obtain ⟨cn, en⟩ := b.nx
  obtain ⟨j⟩ := hp hKP hT w Z c'.Wt c'.O.p0 b.what₂ c'.O.nch b.n c'.O.xd cn ⟨en⟩ ⟨b.rx⟩ b.pin
  exact GlobalTheory.T.series_realization_of_published h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 (w.st Z).toD7 c'.O.nch c'.O.xd
    j.X j.Y j.gal j.field (GlobalTheory.T.galois_hodge_of_cuspidal hL hA hG hR hLG _ _ j.cg).1 (hconds _) c'.nch_tie (j.base hT)

end GlobalTheory.ExportFirst
