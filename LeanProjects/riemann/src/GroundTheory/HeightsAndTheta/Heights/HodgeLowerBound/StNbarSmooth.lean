import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ChartVel
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ) (t : ℝ),
    X.M.atlas.Smooth (X.S.regWeight t) → IsSmoothHerm (X.NbarQ B p q t)

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem NbarSmooth.hyps_of_setting (X : ComponentSetting D O Lt) :
    ∃ t : ℝ, 0 < t ∧ X.M.atlas.Smooth (X.S.regWeight t) := by
  obtain ⟨t, -, ht, hs, -⟩ := NbarChartSemipos.hyps_of_setting X one_pos
  exact ⟨t, ht, hs⟩

theorem Line.NbarSmooth.hyps_inhabited :
    ∃ t : ℝ, 0 < t ∧ (Line.projLineComponentSetting Line.zeroSystem Line.zero_hII).M.atlas.Smooth
      ((Line.projLineComponentSetting Line.zeroSystem Line.zero_hII).S.regWeight t) :=
  LowerBoundFree.NbarSmooth.hyps_of_setting _

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
