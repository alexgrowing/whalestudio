import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRatioOnOverlap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ratio_on_overlap : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → ∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p], ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ‖ψ (χ1 (c1 : Localization.Away (p : R1))) - ψ (χ2 (c2 : Localization.Away (p : R2)))‖ < ‖ψ (χ2 (c2 : Localization.Away (p : R2)))‖ := by
  first | exact @GlobalTheory.FlatModel.unit_ratio_close | exact GlobalTheory.FlatModel.unit_ratio_close | (intros; apply GlobalTheory.FlatModel.unit_ratio_close <;> assumption)
