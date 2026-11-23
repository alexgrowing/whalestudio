import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsContraction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DatumExistsPeriod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.exists_period_domain_param :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H D.p D.q ty → ∃ (B : Set (Fin D.dim → ℂ)) (P : (Fin D.dim → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B ∧ Convex ℝ B ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolPeriods D ty B P ∧ ∀ P', _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P' → ∃! b, b ∈ B ∧ ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' a = h (P b a) := by
  intro E _ _ _ H D g ty hty
  obtain ⟨P₀, hP₀⟩ := _root_.GlobalTheory.PeriodNonempty.exists_isPeriod E H D g ty hty
  obtain ⟨m, B, P, hm, hB, hBc, -, -, hP, huniq⟩ :=
    _root_.GlobalTheory.PeriodChart.period_chart E H D g ty hty P₀ hP₀
  have hdim : m = D.dim := by
    have h2 : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E :=
      IsTotallyComplex.finrank E
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim
    rw [h2] at hm ⊢
    rw [Nat.mul_div_cancel_left _ two_pos]
    linarith
  subst hdim
  exact ⟨B, P, hB, hBc, hP, huniq⟩

end GlobalTheory
