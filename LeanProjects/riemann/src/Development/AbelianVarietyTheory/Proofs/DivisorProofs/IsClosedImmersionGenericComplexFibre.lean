import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open GlobalTheory.HorComp

set_option autoImplicit false

namespace GlobalTheory.HorComp

open Limits in

theorem isPullback_toGenCx {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {Y : Scheme.{0}} {q : Y ⟶ Sp Oz}
    (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) :
    IsPullback (pullback.fst q (spMap (σ.comp β))) (toGenCx j hj σ) j
      (pullback.fst (genStr Z) (spMap σ) ≫ pullback.fst Z.s (spMap β)) := by
  have h1 : IsPullback (pullback.fst (genStr Z) (spMap σ) ≫ pullback.fst Z.s (spMap β))
      (pullback.snd (genStr Z) (spMap σ)) Z.s (spMap (σ.comp β)) := by
    rw [← spMap_comp_spMap]
    exact (IsPullback.of_hasPullback (genStr Z) (spMap σ)).paste_horiz (IsPullback.of_hasPullback Z.s (spMap β))
  refine IsPullback.of_bot ?_ ?_ h1
  · have e : toGenCx j hj σ ≫ pullback.snd (genStr Z) (spMap σ) = pullback.snd q (spMap (σ.comp β)) :=
      pullback.lift_snd _ _ _
    rw [e, hj]
    exact IsPullback.of_hasPullback _ _
  · have e : toGenCx j hj σ ≫ pullback.fst (genStr Z) (spMap σ) = toGen j hj σ := pullback.lift_fst _ _ _
    have e' : toGen j hj σ ≫ pullback.fst Z.s (spMap β) = pullback.fst q (spMap (σ.comp β)) ≫ j :=
      pullback.lift_fst _ _ _
    rw [← e', ← e]
    exact Category.assoc _ _ _

theorem isClosedImmersion_toGenCx : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → IsClosedImmersion (toGenCx jm hq σ) := by
  intro D A N j S κ s σ Y _ q jm hjm hq n _
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_toGenCx jm hq σ) hjm

end GlobalTheory.HorComp
