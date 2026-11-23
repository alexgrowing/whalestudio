import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSecOfNot

set_option autoImplicit false

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

namespace GlobalTheory.ClopenPush

theorem exists_app_eq_res {X Y : Scheme.{0}} (j : Y ⟶ X) [IsClosedImmersion j] (W : Y.Opens) (g : Γ(Y, W))
    (x : Y) (hx : x ∈ W) :
    ∃ (U : X.Opens) (e : j ⁻¹ᵁ U ≤ W) (G : Γ(X, U)), j x ∈ U ∧ j.app U G = resG Y e g := by
  obtain ⟨W', hW', hWW⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.1 W.isOpen
  have hx' : j x ∈ (⟨W', hW'⟩ : X.Opens) := by
    have : x ∈ j ⁻¹' W' := hWW ▸ hx
    exact this
  obtain ⟨U, hU, hxU, hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx'
  have e : j ⁻¹ᵁ U ≤ W := fun z hz => by
    have : z ∈ j ⁻¹' W' := hle hz
    rw [hWW] at this
    exact this
  obtain ⟨G, hG⟩ := j.app_surjective U hU (resG Y e g)
  exact ⟨U, e, G, hxU, hG⟩

theorem liftsFns_of_isClosedImmersion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) [IsClosedImmersion j] (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ), ClopenPush.LiftsFns j hj σ := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z Y q j _ hj σ W g y hy
  obtain ⟨U, e, G, hU, hG⟩ := exists_app_eq_res j W g _ (mem_ptsIn.1 hy)
  have key (y' : CxPts q (σ.comp β)) :
      up j hj σ y' ∈ ptsIn (genStr Z) σ (genι Z ⁻¹ᵁ U) ↔ y' ∈ ptsIn q (σ.comp β) (j ⁻¹ᵁ U) := by
    have h : genι Z ((up j hj σ y').1 (IsLocalRing.closedPoint ℂ)) = j (y'.1 (IsLocalRing.closedPoint ℂ)) :=
      congrArg (fun g : Sp ℂ ⟶ Z.X => g (IsLocalRing.closedPoint ℂ)) (up_ι j hj σ y')
    rw [mem_ptsIn, mem_ptsIn]
    change genι Z _ ∈ U ↔ j _ ∈ U
    rw [h]
  refine ⟨genι Z ⁻¹ᵁ U, (genι Z).app U G, (key y).2 (mem_ptsIn.2 hU), fun y' hy' => ?_⟩
  have h' := (key y').1 hy'
  refine ⟨ptsIn_mono e h', ?_⟩
  rw [← ev_res e h' g, ← hG]
  refine (Points.valR_comp (up j hj σ y').1 (genι Z) U G).symm.trans ?_
  rw [up_ι]
  exact Points.valR_comp y'.1 j U G

end GlobalTheory.ClopenPush
