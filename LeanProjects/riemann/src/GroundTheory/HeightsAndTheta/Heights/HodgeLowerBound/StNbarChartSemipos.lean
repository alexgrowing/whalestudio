import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RegWeightLevi
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarChartSemipos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt), ∃ c : ℝ, 0 < c ∧ ∀ (B p q : ℕ) (t δ : ℝ),
      X.M.atlas.Smooth (X.S.regWeight t) →
      (∀ k : Fin X.S.R.N, ∀ x ∈ X.S.R.mid k, ∀ w : Fin D.n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k x) w) →
      (q : ℝ) * δ ≤ p * c →
      IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t)

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

omit [DecidableEq Ψ] in

theorem NbarChartSemipos.hyps_of_setting (X : ComponentSetting D O Lt) {c : ℝ} (hc : 0 < c) :
    ∃ t δ : ℝ, 0 < t ∧ X.M.atlas.Smooth (X.S.regWeight t) ∧
      (∀ k : Fin X.S.R.N, ∀ x ∈ X.S.R.mid k, ∀ w : Fin D.n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k x) w) ∧
      ((1 : ℕ) : ℝ) * δ ≤ ((1 : ℕ) : ℝ) * c := by
  have hlim : Tendsto (fun t => 4 * X.S.Cη * X.S.e1 t) (𝓝[>] 0) (𝓝 0) := by
    simpa using X.S_tied.e1_tendsto_zero.const_mul (4 * X.S.Cη)
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := eventually_mem_nhdsWithin
  have hev := (X.S.eventually_chartLevi X.S_tied).and (h1.and (hlim.eventually (eventually_le_nhds hc)))
  obtain ⟨t, ⟨hs, hl⟩, ht, hδ⟩ := hev.exists
  exact ⟨t, 4 * X.S.Cη * X.S.e1 t, ht, hs, hl, by simpa using hδ⟩

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

theorem NbarChartSemipos.hyps_inhabited {c : ℝ} (hc : 0 < c) :
    ∃ t δ : ℝ, 0 < t ∧ (projLineComponentSetting zeroSystem zero_hII).M.atlas.Smooth
        ((projLineComponentSetting zeroSystem zero_hII).S.regWeight t) ∧
      (∀ k : Fin (projLineComponentSetting zeroSystem zero_hII).S.R.N, ∀ x ∈ (projLineComponentSetting zeroSystem zero_hII).S.R.mid k,
        ∀ w : Fin (lineData zeroSystem zero_hII).n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi ((projLineComponentSetting zeroSystem zero_hII).S.R.chartFun
          ((projLineComponentSetting zeroSystem zero_hII).S.regWeight t) k)
          ((projLineComponentSetting zeroSystem zero_hII).S.R.chart k x) w) ∧
      ((1 : ℕ) : ℝ) * δ ≤ ((1 : ℕ) : ℝ) * c :=
  LowerBoundFree.NbarChartSemipos.hyps_of_setting _ hc

end Line

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
