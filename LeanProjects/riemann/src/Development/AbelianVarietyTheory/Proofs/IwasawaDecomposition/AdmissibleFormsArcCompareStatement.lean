import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleFormsArcCompare
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_forms_arc_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (b : O →+* A) (a₀ : ArcIn Dw l β A b) (γ γ' : levelForms H l.M' a₀.D₀.X) (h : γ ∈ admitted H l.M' a₀.D₀.X) (h' : γ' ∈ admitted H l.M' a₀.D₀.X) (χ : Sp (PowerSeries A) ⟶ Y.X) (g : PowerSeries A →+* PowerSeries A) (W : Wit Y (withForm a₀ γ h) χ) (W' : Wit Y (withForm a₀ γ' h') (spMap g ≫ χ)) (hD : Out.IsPullDeg g W.P.D.toPre W'.P.D.toPre) (bc : W'.t.G ≅ (Over.pullback (Out.specOf g)).obj W.t.G) (w₁ : LB.Iso W'.P.D.toPre.P.L (a₀.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ))), g.comp (PowerSeries.C (R := A)) = PowerSeries.C → g PowerSeries.X ∈ Ideal.span {PowerSeries.X} → Out.IsPullUnif g hD bc W.P.U W'.P.U → (∀ y, hD.xe (W'.e y) = W.e y) → W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ → HEq W'.w w₁ → Tri W.w hD.w w₁ → ∀ (ν : Out.GtPt a₀.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G) (v' : epsR (PowerSeries A) ⟶ W'.t.G), LieImg W ν v → v'.left ≫ bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g) = spMap (dualMap g) ≫ v.left → LieImg W' ν v' := by
  first | exact @GlobalTheory.ArcSubst.lieImg_subst | exact GlobalTheory.ArcSubst.lieImg_subst | (intros; apply GlobalTheory.ArcSubst.lieImg_subst <;> assumption)
