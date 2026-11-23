import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationUnitsCharts
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_units_charts : ∀ (p n : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X) (Xw : X.Opens)
    (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (J : Type) (Q : J → R)
    (u : ∀ j, (Localization.Away ((p : R) * Q j))ˣ),
    (∀ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ) → (∃ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖) ∧
      ∀ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖ → ∀ ψ : Localization.Away ((p : R) * Q j) →+* ℂ_[p],
        ψ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
          ∀ κ ∈ K (spMap φ ≫ ξ), ‖ψ (u j) - κ‖ < ‖κ‖) →
    (∀ yb' : Sp 𝓞_ℂ_[p] ⟶ X', IsTest p (π ⁻¹ᵁ Xw) yb' → IsTest p Xw (yb' ≫ π)) →
    ∀ (R' : Type) [CommRing R'] (χ : Sp R' ⟶ X') (g : R →+* R') (x' : X'), IsOpenImmersion χ → x' ∈ Set.range χ →
      χ ≫ π = spMap g ≫ ξ →
      (((π ⁻¹ᵁ Xw : X'.Opens) : Set X').Nonempty → ∃ φ : R' →+* 𝓞_ℂ_[p], IsTest p (π ⁻¹ᵁ Xw) (spMap φ ≫ χ)) →
      ((∃ k, (∀ j, g (Q k) ∣ g (Q j)) ∧ g (Q k) ∣ (p : R') ^ n) ∨ ∀ j, (p : R') ^ n ∣ g (Q j)) →
      UnitChartAt p (π ⁻¹ᵁ Xw) (fun yb' => K (yb' ≫ π)) x' := by
  first | exact @GlobalTheory.FlatModel.unitChartAt_of_dvd | exact GlobalTheory.FlatModel.unitChartAt_of_dvd | (intros; apply GlobalTheory.FlatModel.unitChartAt_of_dvd <;> assumption)
