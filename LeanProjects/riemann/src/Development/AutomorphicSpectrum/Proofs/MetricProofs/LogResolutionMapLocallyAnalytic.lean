import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {D e : ℕ} (R : AnLogRes P ⊤ D) {Y : Type*} [TopologicalSpace Y]
  (B : FinHolAtlas e Y) {V : Y → Set Y} {μ : Y → Y → (Σ k, ι k) → ℂ} {h : Y → R.X}

theorem continuous_of_orbit_of_ne (hVo : ∀ y, IsOpen (V y)) (hVm : ∀ y, y ∈ V y)
    (hμ : ∀ y q, B.HoloOn (V y) fun u => μ y u q) (hne : ∀ y k, ∃ i, μ y y ⟨k, i⟩ ≠ 0)
    (hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u))
    (hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μ y y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt, tendsto_iff_ultrafilter]
  intro F hF
  obtain ⟨x, -, hx⟩ := isCompact_univ.ultrafilter_le_nhds (F.map h) (by simp)
  have hth : Tendsto h F (𝓝 x) := hx
  have hUx : ∀ᶠ y' in (F : Filter Y), h y' ∈ R.U x := hth ((R.isOpen_U x).mem_nhds (R.mem_U x))
  have hVy : ∀ᶠ y' in (F : Filter Y), y' ∈ V y := hF ((hVo y).mem_nhds (hVm y))
  have hcr : ∀ k (i i' : ι k), R.lift x x ⟨k, i⟩ * μ y y ⟨k, i'⟩ =
      R.lift x x ⟨k, i'⟩ * μ y y ⟨k, i⟩ := by
    intro k i i'
    have t1 : ∀ q, Tendsto (fun y' => R.lift x (h y') q) F (𝓝 (R.lift x x q)) := fun q =>
      (Proj.continuousAt_of_holoOn R.A (R.holo x q) (R.mem_U x)).tendsto.comp hth
    have t2 : ∀ q, Tendsto (fun y' => μ y y' q) F (𝓝 (μ y y q)) := fun q =>
      (Proj.continuousAt_of_holoOn B (hμ y q) (hVm y)).tendsto.mono_left hF
    refine tendsto_nhds_unique ((t1 ⟨k, i⟩).mul (t2 ⟨k, i'⟩))
      (((t1 ⟨k, i'⟩).mul (t2 ⟨k, i⟩)).congr' ?_)
    filter_upwards [hUx, hVy] with y' h1 h2
    exact Proj.orbit_cross (Proj.local_orbit R hVm hc hh h1 h2) k i' i
  have hxy : SameOrbit (R.lift x x) (μ y y) :=
    Proj.orbit_of_cross (R.mem x x (R.mem_U x)).1 (hne y) hcr
  have hxe : x = h y :=
    R.inj x (h y) (Proj.not_mem_mcPts_top _) (Proj.orbit_trans hxy (Proj.orbit_symm (hh y)))
  rw [← hxe]
  exact hx

end Orbit

theorem holoMap_of_local_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P J : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D D' : ℕ) (R : AnLogRes P J D) (R' : AnLogRes P' J' D') (g : R'.X → R.X), J = ⊤ → (∀ x, ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ R'.lift x x ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts P', ∀ x', SameOrbit z' (R'.lift x' x') → SameOrbit (f z') (R.lift (g x') (g x'))) → HoloMap R'.A R.A g := by
  intro K _ ι _ K' _ ι' _ P J P' J' D D' R R' g hJ hg
  subst hJ
  choose Vs f hVs hxV hf hcomp using hg
  have hcl : ∀ y, ContinuousOn (R'.lift y) (R'.U y) := fun y =>
    continuousOn_pi.2 fun p x hx =>
      (Proj.continuousAt_of_holoOn R'.A (R'.holo y p) hx).continuousWithinAt
  let V : R'.X → Set R'.X := fun y => R'.U y ∩ R'.lift y ⁻¹' Vs y
  let μ : R'.X → R'.X → (Σ k, ι k) → ℂ := fun y u => f y (R'.lift y u)
  have hVo : ∀ y, IsOpen (V y) := fun y =>
    (hcl y).isOpen_inter_preimage (R'.isOpen_U y) (hVs y)
  have hVm : ∀ y, y ∈ V y := fun y => ⟨R'.mem_U y, hxV y⟩
  have hμ : ∀ y q, R'.A.HoloOn (V y) fun u => μ y u q := by
    rintro y q j w ⟨hw, hwV⟩
    have h1 : AnalyticAt ℂ (fun w' => R'.lift y ((R'.A.chart j).symm w')) w :=
      AnalyticAt.pi fun p => R'.holo y p j w ⟨hw, hwV.1⟩
    have h2 : AnalyticAt ℂ (f y ∘ fun w' => R'.lift y ((R'.A.chart j).symm w')) w :=
      AnalyticAt.comp (hf y _ hwV.2) h1
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) q).analyticAt _ |>.comp h2
  have hor : ∀ y, ∀ u ∈ V y, SameOrbit (μ y u) (R.lift (g u) (g u)) := fun y u hu =>
    hcomp y _ ⟨hu.2, R'.mem y u hu.1⟩ u (R'.compat y u u ⟨hu.1, R'.mem_U u⟩)
  have hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u) := fun y y' u hu =>
    Proj.orbit_trans (hor y u hu.1) (Proj.orbit_symm (hor y' u hu.2))
  have hh : ∀ y, SameOrbit (R.lift (g y) (g y)) (μ y y) := fun y =>
    Proj.orbit_symm (hor y y (hVm y))
  have hne : ∀ y k, ∃ i, μ y y ⟨k, i⟩ ≠ 0 := fun y k => by
    obtain ⟨i, hi⟩ := (R.mem (g y) (g y) (R.mem_U _)).1 k
    exact ⟨i, Proj.orbit_ne (hh y) hi⟩
  have hcont : Continuous g := continuous_of_orbit_of_ne R R'.A hVo hVm hμ hne hc hh
  exact ⟨hcont, Proj.analytic_of_orbit R R'.A hVo hVm hμ hc hh hcont⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
