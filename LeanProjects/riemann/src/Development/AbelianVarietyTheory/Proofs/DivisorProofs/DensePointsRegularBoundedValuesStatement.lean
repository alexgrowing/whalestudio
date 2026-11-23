import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensePointsRegularBoundedValues
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_points_regular_bounded_values : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : ℕ) (f : Fin N → Y.Fn),
  (∃ U : Y.X.Opens, (U : Set Y.X).Nonempty ∧ ∀ x ∈ U, ∀ i, RegAt x (f i)) →
  ∃ S : Set Y.X, (∀ x ∈ S, IsClosed ({x} : Set Y.X)) ∧ Dense S ∧ (∀ x ∈ S, ∀ i, RegAt x (f i)) ∧
    ∃ (a : ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support b).Finite ∧ ∀ x ∈ S,
      (∀ (σ : F →+* ℂ) (z : Pts Y σ), under z = x → ∀ i, ‖ratVal (f i) z‖ ≤ a) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y), below y.1 = x → ∀ i,
        e.w (valAt y.1 (f i)) ≤ Real.exp (b v)) := by
  first | exact @GlobalTheory.dense_closedPoints_bounded | exact GlobalTheory.dense_closedPoints_bounded | (intros; apply GlobalTheory.dense_closedPoints_bounded <;> assumption)
