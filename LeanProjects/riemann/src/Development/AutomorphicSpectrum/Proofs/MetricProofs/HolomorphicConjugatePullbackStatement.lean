import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicConjugatePullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_conjugate_pullback : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} (c : X → X), Continuous c → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → ∀ {V : Set X} {g : X → ℂ}, A.HoloOn V g → A.HoloOn (c ⁻¹' V) (fun y => starRingEnd ℂ (g (c y))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.holoOn_conj_comp <;> assumption)
