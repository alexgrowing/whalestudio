import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XAnConj
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem an_conj_symmetrise : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsPotential A Θ → IsPosPot A Θ → ∀ (c : X → X), Continuous c → (∀ x, c (c x) = x) → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → (∀ y, c y ∈ bdry s ↔ y ∈ bdry s) → (∀ y, rW L s (c y) = rW L s y) → ∀ (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ), IsPotential A th → (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re) → (∀ y ∉ bdry s, ph (c y) = ph y) → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → ∃ C' t₀' : ℝ, IsRegFamily A Θ L s th ph (fun t y => (phT t y + phT t (c y)) / 2) C' t₀' ∧ IsRegFamilyC2 A s ph fun t y => (phT t y + phT t (c y)) / 2 :=
  @PositivityTheory.Xgp.t_an_conj

end GlobalTheory.CompanionTheory.Ar.PB
