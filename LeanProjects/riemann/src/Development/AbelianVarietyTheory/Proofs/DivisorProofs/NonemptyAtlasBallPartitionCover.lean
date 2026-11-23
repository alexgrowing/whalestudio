import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem nonempty_cover : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), Nonempty (Cover A) := by
  intro n Y _ _ _ _ _ _ ι La _ A
  classical
  have hε : ∀ x : Y, ∃ ε > 0, ball (A.chart (A.pick x) x) ε ⊆ (A.chart (A.pick x)).target :=
    fun x => Metric.isOpen_iff.1 (A.chart (A.pick x)).open_target _
      ((A.chart (A.pick x)).map_source (A.mem_pick x))
  choose ε hε0 hεb using hε
  let b : ∀ x : Y, ContDiffBump (A.chart (A.pick x) x) := fun x =>
    ⟨ε x / 4, ε x / 2, by linarith [hε0 x], by linarith [hε0 x]⟩
  let β : Y → Y → ℝ := fun x => A.chiC (A.pick x) (b x)
  let K0 : Y → Set (V n) := fun x => closedBall (A.chart (A.pick x) x) (ε x / 2)
  have hK0t : ∀ x, K0 x ⊆ (A.chart (A.pick x)).target := fun x =>
    (closedBall_subset_ball (by linarith [hε0 x])).trans (hεb x)
  have hbs : ∀ x u, (b x) u ≠ 0 → u ∈ K0 x := by
    intro x u hu
    have : u ∈ Function.support (b x) := hu
    rw [(b x).support_eq] at this
    exact ball_subset_closedBall this
  have hβs : ∀ x, A.SmoothFn (β x) := fun x =>
    A.chiC_smooth (b x).contDiff (hbs x) (isCompact_closedBall _ _) (hK0t x)
  have hβ0 : ∀ x y, 0 ≤ β x y := by
    intro x y
    show 0 ≤ A.chiC _ _ y
    unfold WeightedAtlas.chiC
    split_ifs
    · exact (b x).nonneg
    · exact le_rfl
  let U : Y → Set Y := fun x =>
    (A.chart (A.pick x)).source ∩ (A.chart (A.pick x)) ⁻¹' ball (A.chart (A.pick x) x) (ε x / 2)
  have hUo : ∀ x, IsOpen (U x) := fun x =>
    (A.chart (A.pick x)).continuousOn.isOpen_inter_preimage (A.chart (A.pick x)).open_source
      isOpen_ball
  have hUx : ∀ x, x ∈ U x := fun x => ⟨A.mem_pick x, mem_ball_self (by linarith [hε0 x])⟩
  have hUpos : ∀ x y, y ∈ U x → 0 < β x y := by
    rintro x y ⟨hy, hyb⟩
    show 0 < A.chiC _ _ y
    rw [A.chiC_of_mem hy]
    exact (b x).pos_of_mem_ball hyb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hUx y⟩)
  let pt : Fin t.card → Y := fun a => (t.equivFin.symm a).1
  let S : Y → ℝ := fun y => ∑ a, β (pt a) y
  have hS : ∀ y, 0 < S y := by
    intro y
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    have hpt : pt (t.equivFin ⟨x, hxt⟩) = x := by simp [pt]
    have h1 : β (pt (t.equivFin ⟨x, hxt⟩)) y ≤ S y :=
      Finset.single_le_sum (f := fun a => β (pt a) y) (fun a _ => hβ0 (pt a) y)
        (Finset.mem_univ _)
    rw [hpt] at h1
    linarith [hUpos x y hyx]
  have hSs : A.SmoothFn S := by
    intro j
    have : (S ∘ (A.chart j).symm) = fun v => ∑ a, β (pt a) ((A.chart j).symm v) := rfl
    rw [this]
    exact ContDiffOn.sum fun a _ => hβs (pt a) j
  refine ⟨{
    m := t.card
    idx := fun a => A.pick (pt a)
    c := fun a => A.chart (A.pick (pt a)) (pt a)
    r := fun a => 3 * ε (pt a) / 4
    chi := fun a y => β (pt a) y / S y
    r_pos := fun a => by have := hε0 (pt a); positivity
    sub := fun a => (closedBall_subset_ball (by linarith [hε0 (pt a)])).trans (hεb (pt a))
    smooth := ?_
    supp := ?_
    nonneg := fun a y => div_nonneg (hβ0 _ y) (hS y).le
    sum_one := fun y => by rw [← Finset.sum_div]; exact div_self (hS y).ne' }⟩
  · intro a j v hv
    exact ((hβs (pt a) j v hv).div (hSs j v hv) (hS _).ne')
  · intro a
    set x := pt a
    have hKc : IsClosed ((A.chart (A.pick x)).symm '' K0 x) :=
      (A.isCompact_chartImage (isCompact_closedBall _ _) (hK0t x)).isClosed
    refine (closure_minimal ?_ hKc).trans ?_
    · intro y hy
      have hy' : β x y ≠ 0 := fun h0 => hy (by simp only [h0, zero_div])
      by_contra hK
      exact hy' (A.chiC_eq_zero (hbs x) hK)
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨(A.chart (A.pick x)).map_target (hK0t x hu), ?_⟩
      simp only [Set.mem_preimage]
      rw [(A.chart (A.pick x)).right_inv (hK0t x hu)]
      exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hu) (by linarith [hε0 x]))

end GlobalTheory.OTY
