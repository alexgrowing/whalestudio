import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothGlue

theorem continuousAt_of_smoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {N : Set X} {E : X → ℝ} (hN : IsOpen N) (hS : A.SmoothOn N E) {p : X} (hp : p ∈ N) :
    ContinuousAt E p := by
  obtain ⟨j, hj⟩ := A.cover p
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N) :=
    (A.chart j).isOpen_inter_preimage_symm hN
  have hz : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' N := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simpa [Set.mem_preimage, (A.chart j).left_inv hj] using hp
  have h1 : ContinuousAt (E ∘ (A.chart j).symm) (A.chart j p) :=
    ((hS j).continuousOn).continuousAt (hopen.mem_nhds hz)
  have h2 : ContinuousAt (A.chart j) p := (A.chart j).continuousAt hj
  have h1' : ContinuousAt (E ∘ (A.chart j).symm) ((A.chart j) p) := h1
  have h3 : ContinuousAt ((E ∘ (A.chart j).symm) ∘ (A.chart j)) p :=
    ContinuousAt.comp h1' h2
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

theorem eq_of_dense_compl {X : Type} [TopologicalSpace X] {B W : Set X} {f g : X → ℝ}
    (hD : Dense Bᶜ) (hW : IsOpen W) (hf : ∀ p ∈ W, ContinuousAt f p)
    (hg : ∀ p ∈ W, ContinuousAt g p) (hfg : ∀ y ∈ W, y ∉ B → f y = g y) :
    ∀ y ∈ W, f y = g y := by
  intro y hy
  by_contra hne
  have hc : ContinuousAt (fun w => f w - g w) y := (hf y hy).sub (hg y hy)
  have hev : ∀ᶠ w in 𝓝 y, f w - g w ≠ 0 := hc.eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨w, hwB, hw1, hw2⟩ := hD.inter_nhds_nonempty (hev.and (hW.mem_nhds hy))
  exact hw1 (sub_eq_zero.mpr (hfg w hw2 hwB))

theorem glue : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (u : X → ℝ), IsClosed B → Dense Bᶜ → (∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ B → E y = u y) → ∃ u' : X → ℝ, A.Smooth u' ∧ ∀ y ∉ B, u' y = u y := by
  intro e X _ A B u _ hD h
  classical
  choose N E hN hx hS hE using h
  have hagree : ∀ x y, ∀ w ∈ N x ∩ N y, E x w = E y w := by
    intro x y
    refine eq_of_dense_compl hD ((hN x).inter (hN y))
      (fun p hp => continuousAt_of_smoothOn A (hN x) (hS x) hp.1)
      (fun p hp => continuousAt_of_smoothOn A (hN y) (hS y) hp.2) ?_
    intro w hw hwB
    rw [hE x w hw.1 hwB, hE y w hw.2 hwB]
  refine ⟨fun y => if y ∈ B then E y y else u y, ?_, ?_⟩
  · have hu' : ∀ x, ∀ y ∈ N x, (if y ∈ B then E y y else u y) = E x y := by
      intro x y hy
      by_cases hB : y ∈ B
      · rw [if_pos hB]
        exact hagree y x y ⟨hx y, hy⟩
      · rw [if_neg hB]
        exact (hE x y hy hB).symm
    intro j z hz
    have hzt : z ∈ (A.chart j).target := hz.1
    set x := (A.chart j).symm z with hxdef
    have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' N x) :=
      (A.chart j).isOpen_inter_preimage_symm (hN x)
    have hzm : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' N x := ⟨hzt, hx x⟩
    have hc : ContDiffAt ℝ ∞ (E x ∘ (A.chart j).symm) z :=
      (hS x j).contDiffAt (hopen.mem_nhds hzm)
    refine (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hopen.mem_nhds hzm] with w hw
    exact hu' x _ hw.2
  · intro y hy
    simp [hy]

end GlobalTheory.CompanionTheory.SmoothGlue
