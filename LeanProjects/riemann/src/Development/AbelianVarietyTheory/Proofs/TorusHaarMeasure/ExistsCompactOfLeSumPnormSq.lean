import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealFlowPeriodsSpanEqTop

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

namespace CuspCompact

theorem exists_sum_exp_lt {N : ℕ} (C c : Fin N → ℝ) (hc : ∀ k, 0 < c k) (c0 : ℝ) (h0 : 0 < c0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      ∑ k, C k * Real.exp (-2 * Real.pi * c k / s) < c0 := by
  have ht : Filter.Tendsto (fun s : ℝ => ∑ k, C k * Real.exp (-2 * Real.pi * c k / s))
      (𝓝[>] 0) (𝓝 (∑ k : Fin N, C k * 0)) := by
    refine tendsto_finsetSum _ fun k _ => Filter.Tendsto.const_mul _ ?_
    refine Real.tendsto_exp_atBot.comp ?_
    have hneg : -2 * Real.pi * c k < 0 := by
      have := mul_pos Real.pi_pos (hc k)
      linarith
    exact (Filter.Tendsto.const_mul_atTop_of_neg hneg (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))).congr
      fun s => (div_eq_mul_inv _ _).symm
  simp only [mul_zero, Finset.sum_const_zero] at ht
  have hev := ht.eventually (gt_mem_nhds h0)
  obtain ⟨δ, hδ, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  exact ⟨δ, hδ, fun s hs hsδ => hsub ⟨hs, hsδ⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_compact_of_le_sum_pnorm_sq :
    LineBundleFirstBoundGlobalGeneration (E := E) → MahlerCompactnessCriterion (E := E) →
    ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (c0 : ℝ), 0 < c0 →
    ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom,
      c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 →
        ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C := by
  intro hLa hM2 r X Xa c0 h0
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨X.dom, Set.subsingleton_of_subsingleton.isCompact, subset_rfl, fun x hx _ => ?_⟩
    refine ⟨1, X.Γ.one_mem, x, fun τ => ⟨by simp, fun a => a.elim0⟩, ?_⟩
    rwa [Subsingleton.elim (lact 1 (rmul x x)) x]
  have hpos := (hLa r X hr).2.2
  choose c hc hcw using fun k => spectralGap_holds r X Xa.L (Xa.w k) (Xa.w_van k).1
  choose C hC using fun k => cuspidalDecay_holds r X Xa.L (Xa.w k) (c k) (hc k).le (hcw k)
  obtain ⟨δ, hδ, hlt⟩ := exists_sum_exp_lt C c hc c0 h0
  obtain ⟨K, hK, hKd, hKx⟩ := hM2 r X (Real.sqrt δ) (Real.sqrt_pos.2 hδ)
  refine ⟨K, hK, hKd, fun x hx hle => hKx x hx ?_⟩
  have hs : 0 < X.firstMinimumSq x := Real.sqrt_pos.1 (hpos x hx)
  refine Real.sqrt_le_sqrt (not_lt.1 fun h => ?_)
  have h1 := hlt _ hs h
  have h2 : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤
      ∑ k, C k * Real.exp (-2 * Real.pi * c k / X.firstMinimumSq x) :=
    Finset.sum_le_sum fun k _ => hC k x hx
  linarith

end CuspCompact

end GlobalTheory
