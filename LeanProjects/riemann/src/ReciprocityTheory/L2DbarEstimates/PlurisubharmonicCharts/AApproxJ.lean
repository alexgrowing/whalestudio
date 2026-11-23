import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxF

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

structure CutData (Sf : Finset Y) where
  β : Y → V n → ℝ
  r1 : Y → ℝ
  r2 : Y → ℝ
  W : Y → Set Y
  smooth : ∀ P, ContDiff ℝ ∞ (β P)
  one : ∀ P, ∀ u ∈ closedBall (A.chart (A.pick P) P) (r1 P), β P u = 1
  supp : ∀ P, ∀ u, β P u ≠ 0 → u ∈ closedBall (A.chart (A.pick P) P) (r2 P)
  sub : ∀ P ∈ Sf, closedBall (A.chart (A.pick P) P) (r2 P) ⊆
    (A.chart (A.pick P)).target ∩ (A.chart (A.pick P)).symm ⁻¹' W P
  disj : ∀ P ∈ Sf, ∀ Q ∈ Sf, P ≠ Q → Disjoint (W P) (W Q)

variable {A}

namespace CutData

variable {Sf : Finset Y} (D : CutData A Sf)

def K (P : Y) : Set Y := (A.chart (A.pick P)).symm '' closedBall (A.chart (A.pick P) P) (D.r2 P)

def T (P : Y) : Set Y := (A.chart (A.pick P)).symm ''
  (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P))

def χ (P : Y) : Y → ℝ := A.chiC (A.pick P) (D.β P)

theorem K_sub {P : Y} (hP : P ∈ Sf) : D.K P ⊆ (A.chart (A.pick P)).source ∩ D.W P := by
  rintro _ ⟨u, hu, rfl⟩
  have h := D.sub P hP hu
  exact ⟨(A.chart (A.pick P)).map_target h.1, h.2⟩

theorem K_compact {P : Y} (hP : P ∈ Sf) : IsCompact (D.K P) :=
  A.isCompact_chartImage (isCompact_closedBall _ _) fun _ hu => (D.sub P hP hu).1

theorem T_sub_K (P : Y) : D.T P ⊆ D.K P := image_mono diff_subset

theorem T_compact {P : Y} (hP : P ∈ Sf) : IsCompact (D.T P) :=
  A.isCompact_chartImage ((isCompact_closedBall _ _).diff isOpen_ball)
    fun _ hu => (D.sub P hP hu.1).1

theorem χ_smooth {P : Y} (hP : P ∈ Sf) : A.SmoothFn (D.χ P) :=
  A.chiC_smooth (D.smooth P) (D.supp P) (isCompact_closedBall _ _) fun _ hu => (D.sub P hP hu).1

theorem χ_supp (P : Y) (y : Y) (hy : D.χ P y ≠ 0) : y ∈ D.K P := by
  by_contra h; exact hy (A.chiC_eq_zero (D.supp P) h)

theorem not_mem_K {P Q : Y} (hP : P ∈ Sf) (hQ : Q ∈ Sf) (hPQ : P ≠ Q) {y : Y}
    (hy : y ∈ D.K P) : y ∉ D.K Q := fun h =>
  Set.disjoint_left.1 (D.disj P hP Q hQ hPQ) (D.K_sub hP hy).2 (D.K_sub hQ h).2

theorem eventually_χ_zero {P : Y} (hP : P ∈ Sf) (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hy : y ∉ D.K P) : ∀ᶠ v in 𝓝 (A.chart j y), D.χ P ((A.chart j).symm v) = 0 := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (D.K P)ᶜ) :=
    (A.chart j).isOpen_inter_preimage_symm (D.K_compact hP).isClosed.isOpen_compl
  filter_upwards [hopen.mem_nhds ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hy]⟩]
    with v hv
  by_contra h; exact hv.2 (D.χ_supp P _ h)

theorem eventually_χ_one {P : Y} (j : ι) {y : Y} (hj : y ∈ (A.chart j).source)
    (hyP : y ∈ (A.chart (A.pick P)).source)
    (hb : A.chart (A.pick P) y ∈ ball (A.chart (A.pick P) P) (D.r1 P)) :
    ∀ᶠ v in 𝓝 (A.chart j y), (A.chart j).symm v ∈ (A.chart (A.pick P)).source ∧
      D.χ P ((A.chart j).symm v) = 1 := by
  have hc : ContinuousOn ((A.chart (A.pick P)) ∘ (A.chart j).symm) (ovl A.chart j (A.pick P)) :=
    (A.trans_contDiffOn j (A.pick P)).continuousOn
  have hopen : IsOpen (ovl A.chart j (A.pick P) ∩ ((A.chart (A.pick P)) ∘ (A.chart j).symm) ⁻¹'
      ball (A.chart (A.pick P) P) (D.r1 P)) :=
    hc.isOpen_inter_preimage (A.isOpen_ovl j _) isOpen_ball
  have hmem : A.chart j y ∈ ovl A.chart j (A.pick P) ∩ ((A.chart (A.pick P)) ∘ (A.chart j).symm) ⁻¹'
      ball (A.chart (A.pick P) P) (D.r1 P) :=
    ⟨A.mem_ovl hj hyP, by simpa [Function.comp, (A.chart j).left_inv hj] using hb⟩
  filter_upwards [hopen.mem_nhds hmem] with v hv
  refine ⟨hv.1.2, ?_⟩
  rw [χ, A.chiC_of_mem hv.1.2]
  exact D.one P _ (ball_subset_closedBall hv.2)

end CutData

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
