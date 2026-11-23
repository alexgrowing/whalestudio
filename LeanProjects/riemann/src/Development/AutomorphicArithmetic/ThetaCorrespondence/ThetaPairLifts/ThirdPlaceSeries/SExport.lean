import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportAtBundlesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SHodgeDghOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportFIsBuiltETyz

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
namespace GlobalTheory.ExportFirst
theorem exportF_isBuiltE_alt_alt : _root_.GlobalTheory.ExportFirst.exportF_isBuiltE_tyz := by
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
  exact _root_.GlobalTheory.T.series_realization_of_published_alt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 (w.st Z).toD7 c'.O.nch c'.O.xd
    j.X j.Y j.gal j.field (_root_.UpperTheory.GalS.ghOf'_alt hL hA hG hR hLG _ _ j.cg j.gal.lab) (hconds _) c'.nch_tie (j.base hT)
end GlobalTheory.ExportFirst
end
