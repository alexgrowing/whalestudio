import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPointGenericFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_point_generic_fibre : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x : X) (φ : cR h x →+* 𝓞_ℂ_[p]) (yb : Sp 𝓞_ℂ_[p] ⟶ X), spMap φ ≫ cξ h x = yb → ∀ y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s, y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb → ∀ (e : ((glueLB h).pull yb).Gen) (cc : ℂ_[p]ˣ), GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord s (glueLB h) (sigGen h s) yb y e cc → ∃ ψ : Localization.Away (p : cR h x) →+* ℂ_[p], ψ.comp (algebraMap (cR h x) _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ ∧ ‖ψ (cu h x : Localization.Away (p : cR h x))‖ = ‖(cc : ℂ_[p])‖ := by
  first | exact @GlobalTheory.UnitGlue.EvalPt.evalPt_norm | exact GlobalTheory.UnitGlue.EvalPt.evalPt_norm | (intros; apply GlobalTheory.UnitGlue.EvalPt.evalPt_norm <;> assumption)
