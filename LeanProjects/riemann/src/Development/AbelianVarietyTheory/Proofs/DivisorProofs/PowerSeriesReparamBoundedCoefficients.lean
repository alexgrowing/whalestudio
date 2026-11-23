import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem regroup_fib_tsum {X M : Type} [AddCommMonoid M] [TopologicalSpace M] (n : X → ℕ) (i : ℕ)
    (h : {α | n α = i}.Finite) (f : X → M) :
    ∑' b : n ⁻¹' {i}, f b = ∑ α ∈ h.toFinset, f α := by
  have hs : n ⁻¹' {i} = (h.toFinset : Set X) := by ext; simp
  rw [← Finset.tsum_subtype', ← hs]

theorem lattice_series_regroup : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) (n : X → ℕ) (π : C) (a : X → C) (b : ℝ), π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ α, ‖a α‖ ≤ b * ‖π‖ ^ n α) → ∃ Θ : PowerSeries C, (∀ i, ‖PowerSeries.coeff i Θ‖ ≤ max b 0) ∧ ∑' i, PowerSeries.coeff i Θ * π ^ i = ∑' α, a α ∧ ∀ (e : C →+* ℂ) (u : ℂ), (Summable fun α => ‖e (a α) * (u / e π) ^ n α‖) → (Summable fun i => ‖e (PowerSeries.coeff i Θ) * u ^ i‖) ∧ ∑' i, e (PowerSeries.coeff i Θ) * u ^ i = ∑' α, e (a α) * (u / e π) ^ n α := by
  intro C _ _ _ X n π a b hπ0 hπ1 hfin hb
  classical
  have hmem : ∀ i α, α ∈ (hfin i).toFinset ↔ n α = i := fun i α => by simp
  have hn : Filter.Tendsto n Filter.cofinite Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun N => Filter.eventually_cofinite.2 ?_
    refine ((Set.finite_lt_nat N).biUnion fun i _ => hfin i).subset ?_
    intro α hα
    simp only [Set.mem_setOf_eq, not_le] at hα
    exact Set.mem_biUnion (x := n α) hα rfl
  have hpow : Filter.Tendsto (fun α => b * ‖π‖ ^ n α) Filter.cofinite (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ1).comp hn).const_mul b
  have ha0 : Filter.Tendsto a Filter.cofinite (nhds 0) := squeeze_zero_norm hb hpow
  have ha : Summable a := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ha0
  refine ⟨PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i, ?_, ?_, ?_⟩
  · intro i
    rw [PowerSeries.coeff_mk]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (le_max_right _ _) fun α hα => ?_
    have hpi : 0 < ‖π‖ ^ i := pow_pos (norm_pos_iff.2 hπ0) _
    rw [norm_div, norm_pow, div_le_iff₀ hpi]
    have := hb α
    rw [(hmem i α).1 hα] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpi.le)
  · rw [← ((ha.hasSum.tsum_fiberwise n).tsum_eq)]
    refine tsum_congr fun i => ?_
    rw [PowerSeries.coeff_mk, regroup_fib_tsum n i (hfin i), Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => div_mul_cancel₀ _ (pow_ne_zero _ hπ0)
  · intro e u hsum
    have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
    have hkey : ∀ i, e (PowerSeries.coeff i (PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i)) * u ^ i
        = ∑ α ∈ (hfin i).toFinset, e (a α) * (u / e π) ^ n α := by
      intro i
      rw [PowerSeries.coeff_mk, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [(hmem i α).1 hα, map_div₀, map_pow, div_pow]
      field_simp
    simp_rw [hkey]
    have hf : Summable fun α => e (a α) * (u / e π) ^ n α := hsum.of_norm
    refine ⟨?_, ?_⟩
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_sum_le _ _) ?_
      have := (hsum.hasSum.tsum_fiberwise n).summable
      exact this.congr fun i => regroup_fib_tsum n i (hfin i) (fun α => ‖e (a α) * (u / e π) ^ n α‖)
    · rw [← ((hf.hasSum.tsum_fiberwise n).tsum_eq)]
      exact tsum_congr fun i => (regroup_fib_tsum n i (hfin i) _).symm

end GlobalTheory.MBLow
