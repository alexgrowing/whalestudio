import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTTop
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTopNMixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem ComponentSetting.mixN_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
    (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) : X.mixN B (D.n + 1) t = arLimFun X.H X.S B t := by
  unfold ComponentSetting.mixN arLimFun
  congr 1
  funext j
  simp [j.is_lt]

theorem StokesLimitTTop.proof (hE : TopNMixedExpand.Statement) (hM : TopNMixedLimit.Statement) :
    StokesLimitTTop.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hAr hp hpq
  have hlim : ∀ k ∈ Finset.range (D.n + 2), ∃ L : ℝ, Tendsto (X.mixN B k) (𝓝[>] 0) (𝓝 L) := by
    intro k hk
    rcases Nat.lt_or_ge k (D.n + 1) with h | h
    · exact hM II Ψ K ι Ω E D O Lt X B hII hAr k (Nat.lt_succ_iff.1 h)
    · have hk' : k = D.n + 1 := le_antisymm (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) h
      subst hk'
      obtain ⟨L, hL⟩ := hAr
      exact ⟨L, hL.congr fun t => (X.mixN_top B t).symm⟩
  choose! L hL using hlim
  refine ⟨∑ k ∈ Finset.range (D.n + 2), ((D.n + 1).choose k : ℝ) * ((p : ℝ) / q) ^ (D.n + 1 - k) * L k, ?_⟩
  refine Tendsto.congr' ((hE II Ψ K ι Ω E D O Lt X B p q hII hp hpq).mono fun t ht => ht.symm) ?_
  exact tendsto_finsetSum _ fun k hk => (hL k hk).const_mul _

end GroundTheory.Heights₂.Heights.LowerBoundFree
