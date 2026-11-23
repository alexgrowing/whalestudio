import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

def bsTr (la : La) (U : Set Y) (a : ι → Y → ℂ) : Prop :=
  ∀ i j y, y ∈ U → y ∈ (A.chart i).source → y ∈ (A.chart j).source → a i y = A.g la i j y * a j y

theorem bsA_g_zero {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    A.g 0 i j y = 1 := by
  have h := A.g_add 0 0 i j y hi hj
  rw [add_zero] at h
  have hne := A.g_ne 0 i j y hi hj
  have h2 : A.g 0 i j y * (A.g 0 i j y - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hne
  · exact sub_eq_zero.mp h3

theorem bsA_g_nsmul (la : La) (k : ℕ) {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : A.g (k • la) i j y = A.g la i j y ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero]; exact bsA_g_zero A hi hj
  | succ k ih => rw [succ_nsmul, A.g_add _ _ i j y hi hj, ih, pow_succ]

theorem bsA_ph_zero {i : ι} {y : Y} (hi : y ∈ (A.chart i).source) : A.ph 0 i y = 0 := by
  have h := A.ph_add 0 0 i y hi
  rw [add_zero] at h
  linarith

theorem bsA_ph_nsmul (la : La) (k : ℕ) {i : ι} {y : Y} (hi : y ∈ (A.chart i).source) :
    A.ph (k • la) i y = k * A.ph la i y := by
  induction k with
  | zero => rw [zero_nsmul, bsA_ph_zero A hi]; simp
  | succ k ih => rw [succ_nsmul, A.ph_add _ _ i y hi, ih]; push_cast; ring

theorem bsA_ph_sub (la mu : La) {i : ι} {y : Y} (hi : y ∈ (A.chart i).source) :
    A.ph (la - mu) i y = A.ph la i y - A.ph mu i y := by
  have h := A.ph_add (la - mu) mu i y hi
  rw [sub_add_cancel] at h
  linarith

theorem bsA_tr_of_isSecOn {la : La} {U : Set Y} {a : ι → Y → ℂ} (h : A.IsSecOn la U a) :
    bsTr A la U a := by
  unfold WeightedAtlas.IsSecOn at h
  exact h.2

theorem bsA_isSecOn_mono {la : La} {U V : Set Y} {a : ι → Y → ℂ} (h : A.IsSecOn la U a)
    (hVU : V ⊆ U) : A.IsSecOn la V a := by
  unfold WeightedAtlas.IsSecOn at h ⊢
  exact And.intro (fun i => (h.1 i).mono (fun v hv => ⟨hv.1, hVU hv.2⟩))
    (fun i j y hy => h.2 i j y (hVU hy))

theorem bsA_tr_mul {la mu : La} {U : Set Y} {a b : ι → Y → ℂ} (ha : bsTr A la U a)
    (hb : bsTr A mu U b) : bsTr A (la + mu) U (fun i y => a i y * b i y) := by
  unfold bsTr at ha hb ⊢
  intro i j y hy hi hj
  show a i y * b i y = A.g (la + mu) i j y * (a j y * b j y)
  rw [ha i j y hy hi hj, hb i j y hy hi hj, A.g_add la mu i j y hi hj]
  ring

theorem bsA_tr_pow {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) (k : ℕ) :
    bsTr A (k • la) U (fun i y => a i y ^ k) := by
  unfold bsTr at ha ⊢
  intro i j y hy hi hj
  show a i y ^ k = A.g (k • la) i j y * a j y ^ k
  rw [ha i j y hy hi hj, bsA_g_nsmul A la k hi hj, mul_pow]

theorem bsA_tr_ratio {la : La} {U : Set Y} {a b : ι → Y → ℂ} (ha : bsTr A la U a)
    (hb : bsTr A la U b) {i j : ι} {y : Y} (hy : y ∈ U) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : a i y / b i y = a j y / b j y := by
  unfold bsTr at ha hb
  rw [ha i j y hy hi hj, hb i j y hy hi hj, mul_div_mul_left _ _ (A.g_ne la i j y hi hj)]

theorem bsA_ne_of_tr {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) {i j : ι}
    {y : Y} (hy : y ∈ U) (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source)
    (h : a j y ≠ 0) : a i y ≠ 0 := by
  unfold bsTr at ha
  rw [ha i j y hy hi hj]
  exact mul_ne_zero (A.g_ne la i j y hi hj) h

theorem bsA_nsq_chart {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) {i : ι} {y : Y}
    (hy : y ∈ U) (hi : y ∈ (A.chart i).source) :
    A.nsq la a y = ‖a i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  have hp := A.mem_pick y
  unfold bsTr at ha
  unfold WeightedAtlas.nsq
  have hg : 0 < ‖A.g la (A.pick y) i y‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (A.g_ne la (A.pick y) i y hp hi)) 2
  rw [ha (A.pick y) i y hy hp hi, A.ph_trans la (A.pick y) i y hp hi, norm_mul, mul_pow, neg_sub,
    sub_eq_add_neg, Real.exp_add, Real.exp_log hg]
  ring

theorem continuousOn_section_chart {la : La} {a : ι → Y → ℂ} (ha : A.IsSec la a) (i : ι) :
    ContinuousOn (a i) (A.chart i).source := by
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at ha
  have h1 := (ha.1 i).continuousOn
  have h2 : ContinuousOn ((a i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun z hz => ⟨(A.chart i).map_source hz, Set.mem_univ _⟩)
  refine h2.congr ?_
  intro z hz
  simp only [Function.comp_apply, (A.chart i).left_inv hz]

theorem bsA_ph_cont (la : La) (i : ι) : ContinuousOn (A.ph la i) (A.chart i).source := by
  have h1 := (A.smooth_ph la i).continuousOn
  have h2 : ContinuousOn ((A.ph la i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun z hz => (A.chart i).map_source hz)
  refine h2.congr ?_
  intro z hz
  simp only [Function.comp_apply, (A.chart i).left_inv hz]

theorem bsA_nsq_cont {la : La} {a : ι → Y → ℂ} (ha : A.IsSec la a) : Continuous (A.nsq la a) := by
  have htr : bsTr A la Set.univ a := bsA_tr_of_isSecOn A (U := Set.univ) ha
  rw [continuous_iff_continuousAt]
  intro y
  have hs : (A.chart (A.pick y)).source ∈ 𝓝 y :=
    (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousOn (fun z => ‖a (A.pick y) z‖ ^ 2 * Real.exp (-A.ph la (A.pick y) z))
      (A.chart (A.pick y)).source :=
    ((continuousOn_section_chart A ha (A.pick y)).norm.pow 2).mul ((bsA_ph_cont A la (A.pick y)).neg.rexp)
  refine (hc.continuousAt hs).congr ?_
  filter_upwards [hs] with z hz
  exact (bsA_nsq_chart A htr (Set.mem_univ z) hz).symm

theorem bsA_sqn_cont {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} (hw : ∀ k, A.IsSec la (w k)) :
    Continuous (A.sqn la w) := by
  show Continuous (fun y => ∑ k, A.nsq la (w k) y)
  exact continuous_finset_sum _ (fun k _ => bsA_nsq_cont A (hw k))

theorem bsA_nsq_nonneg (la : La) (a : ι → Y → ℂ) (y : Y) : 0 ≤ A.nsq la a y := by
  unfold WeightedAtlas.nsq
  positivity

theorem bsA_nsq_pos {la : La} {a : ι → Y → ℂ} {y : Y} (h : a (A.pick y) y ≠ 0) :
    0 < A.nsq la a y := by
  unfold WeightedAtlas.nsq
  exact mul_pos (pow_pos (norm_pos_iff.mpr h) 2) (Real.exp_pos _)

theorem bsA_sqn_pos {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {y : Y}
    (h : ∃ k, w k (A.pick y) y ≠ 0) : 0 < A.sqn la w y := by
  obtain ⟨k, hk⟩ := h
  show 0 < ∑ k, A.nsq la (w k) y
  exact Finset.sum_pos' (fun m _ => bsA_nsq_nonneg A la (w m) y) ⟨k, Finset.mem_univ _, bsA_nsq_pos A hk⟩

end

end ReciprocityTheory.L2DbarEstimates.Y
