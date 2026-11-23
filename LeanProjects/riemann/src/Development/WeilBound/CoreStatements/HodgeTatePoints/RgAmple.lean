import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsProdPolAV

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace PositivityTheory.HtPt.Rg

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CM GlobalTheory.LamF GlobalTheory.CechPic GlobalTheory.TripleProd ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM in

theorem ample_prod : ∀ (R : Type) [CommRing R] (A A' : Over (Spec (CommRingCat.of R))) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → IsAbelianScheme A' → L'.IsLB → Out.RelAmple A' L' → IsAbelianScheme (A ⊗ A') ∧ ∃ M : LB (A ⊗ A').left, M.IsLB ∧ Out.RelAmple (A ⊗ A') M := by
  intro R _ A A' _ _ L L' hA hL hLa hA' hL' hLa'
  have hAA := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A' hA hA'
  refine ⟨hAA, ?_⟩
  haveI : IsProper (A ⊗ A').hom := hAA.proper
  have hP : IsPullback (fst A A').left (snd A A').left A.hom A'.hom :=
    Over.isPullback_of_binaryFan_isLimit _ (CartesianMonoidalCategory.tensorProductIsBinaryProduct A A')
  have hp := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hL (fst A A').left
  have hq := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hL' (snd A A').left
  have hN := GlobalTheory.CechPic.isLB_tens hp hq
  have hAmp := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A hL hLa
  have hAmp' := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A' hL' hLa'
  have h1 := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_div hN hp
  have h2 := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_div h1 hq
  have hgen : ∃ t : (((GlobalTheory.CechPic.tens (L.pull (fst A A').left) (L'.pull (snd A A').left)).div
      (L.pull (fst A A').left)).div (L'.pull (snd A A').left)).Gen, t.IsGen := by
    rw [← GlobalTheory.CechPic.cls_eq_zero_iff h2, GlobalTheory.CechPic.cls_div h1 hq h2, GlobalTheory.CechPic.cls_div hN hp h1,
      GlobalTheory.CechPic.cls_tens hp hq hN]
    abel
  have hNamp := GlobalTheory.IsAmpleLB.box hAmp hAmp' hN hP hgen
  exact ⟨_, hN, (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine (A ⊗ A') hN).2 hNamp⟩

end PositivityTheory.HtPt.Rg
