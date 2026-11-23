import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BiholomorphicLiftSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biholomorphic_lift_system : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}, J = ⊤ → ∀ {e : ℕ} (R : AnLogRes P J e) {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (g : X → R.X) (h : R.X → X), (∀ y, g (h y) = y) → (∀ x, h (g x) = x) → HoloMap A R.A g → HoloMap R.A A h → IsLiftSys A P (fun x => g ⁻¹' R.U (g x)) (fun x y => R.lift (g x) (g y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop.isLiftSys_of_top <;> assumption)
