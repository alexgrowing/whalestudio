import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singular_weight_monotone_regularization : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsPotential A Θ → IsPosPot A Θ → (∀ th ph C₅ C₅', C₅ ≤ C₅' → IsSingWeight A L s th ph C₅ → IsSingWeight A L s th ph C₅') ∧ (∀ th ph phT C t₀ C' t₀', |C| ≤ C' → 0 < t₀' → t₀' ≤ t₀ → t₀' ≤ Real.exp (-1) → IsRegFamily A Θ L s th ph phT C t₀ → IsPotential A th → IsRegFamily A Θ L s th ph phT C' t₀') ∧ ∀ th u, IsPotential A th → A.Smooth u → IsPsh A (th + LocPot.ofFun u) → ∃ C₀, IsSingWeight A L s th u C₀ ∧ IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧ IsRegFamilyC2 A s u (fun _ => u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members | exact GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members <;> assumption)
