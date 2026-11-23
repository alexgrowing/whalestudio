import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRatioOnChartOverlap
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
theorem _root_.GlobalTheory.T.unit_ratio_on_chart_overlap : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X) (A : Type) [CommRing A] (w : Sp A ⟶ X) (a1 : cR h x →+* A) (a2 : cR h y →+* A), IsOpenImmersion w → spMap a1 ≫ cξ h x = w → spMap a2 ≫ cξ h y = w → Set.range w = Set.range (cξ h x) ∩ Set.range (cξ h y) → ∀ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical → (∀ (χ1 : Localization.Away (p : cR h x) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : cR h y) →+* Localization.Away (p : A)), χ1.comp (algebraMap (cR h x) _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap (cR h y) _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (cu h y : Localization.Away (p : cR h y)) = χ1 (cu h x : Localization.Away (p : cR h x))) → ∃ u' : Γ(X, Uc h x ⊓ Uc h y)ˣ, RatioProp h x y u' := by
  first | exact @GlobalTheory.UnitGlueTransport.ratioProp_of_chart | exact GlobalTheory.UnitGlueTransport.ratioProp_of_chart | (intros; apply GlobalTheory.UnitGlueTransport.ratioProp_of_chart <;> assumption)
