import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qk29.dot.{v} :
    {ι : Type v} → (ι →₀ ℕ) → (ι → ℝ) → ℝ :=
    fun {ι : Type v} (n : ι →₀ ℕ) (r : ι → ℝ) ↦ n.sum fun (i : ι) (k : ℕ) ↦ (↑k : ℝ) * r i

noncomputable def UpperTheory.Reformulated.B.Qk29.MonoWtGe.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → ℝ → (ι → ℝ) → ℝ → (ι →₀ ℕ) → K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (n : ι →₀ ℕ) (c : K) ↦
      ‖c‖ ≤ pi ^ (w - UpperTheory.Reformulated.B.Qk29.dot n r)

noncomputable def UpperTheory.Reformulated.B.Qk29.WtGe.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → ℝ → (ι → ℝ) → ℝ → MvPowerSeries ι K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (pi : ℝ) (r : ι → ℝ) (w : ℝ) (f : MvPowerSeries ι K) ↦
      ∀ (n : ι →₀ ℕ), UpperTheory.Reformulated.B.Qk29.MonoWtGe pi r w n ((MvPowerSeries.coeff n : MvPowerSeries ι K → K) f)

private theorem UpperTheory.Reformulated.B.Qk29.dot_add {ι : Type*} (a b : ι →₀ ℕ) (r : ι → ℝ) :
    UpperTheory.Reformulated.B.Qk29.dot (a + b) r = UpperTheory.Reformulated.B.Qk29.dot a r + UpperTheory.Reformulated.B.Qk29.dot b r := by
  unfold UpperTheory.Reformulated.B.Qk29.dot
  apply Finsupp.sum_add_index'
  · intro i; simp
  · intro i m n; push_cast; ring

private theorem UpperTheory.Reformulated.B.Qk29.wtGe_one {K : Type*} [NormedField K] {ι : Type*} {pi : ℝ}
    (hpi : 0 < pi) (r : ι → ℝ) : UpperTheory.Reformulated.B.Qk29.WtGe pi r 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe
  rw [MvPowerSeries.coeff_one]
  split_ifs with h
  · subst h
    simp [UpperTheory.Reformulated.B.Qk29.dot]
  · rw [norm_zero]
    exact (Real.rpow_pos_of_pos hpi _).le

private theorem UpperTheory.Reformulated.B.Qk29.wtGe_mul {K : Type*} [NormedField K] {ι : Type*}
    [IsUltrametricDist K] {pi : ℝ} (hpi : 0 < pi) {r : ι → ℝ} {a b : ℝ}
    {f g : MvPowerSeries ι K} (hf : UpperTheory.Reformulated.B.Qk29.WtGe pi r a f)
    (hg : UpperTheory.Reformulated.B.Qk29.WtGe pi r b g) : UpperTheory.Reformulated.B.Qk29.WtGe pi r (a + b) (f * g) := by
  classical
  intro n
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe
  rw [MvPowerSeries.coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_pos_of_pos hpi _).le
  intro p hp
  have hn : p.1 + p.2 = n := by simpa using hp
  have h1 := hf p.1
  have h2 := hg p.2
  unfold UpperTheory.Reformulated.B.Qk29.MonoWtGe at h1 h2
  have he : a + b - UpperTheory.Reformulated.B.Qk29.dot n r =
      (a - UpperTheory.Reformulated.B.Qk29.dot p.1 r) + (b - UpperTheory.Reformulated.B.Qk29.dot p.2 r) := by
    rw [← hn, UpperTheory.Reformulated.B.Qk29.dot_add]; ring
  rw [he, Real.rpow_add hpi, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_pos_of_pos hpi _).le

theorem UpperTheory.Reformulated.B.Qk29.wtGe_prod.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} [IsUltrametricDist K] {pi : ℝ},
      (0 : ℝ) < pi →
        ∀ {r : ι → ℝ} {α : Type w} (s : Finset α) (wt : α → ℝ) (F : α → MvPowerSeries ι K),
          (∀ i ∈ s, UpperTheory.Reformulated.B.Qk29.WtGe pi r (wt i) (F i)) → UpperTheory.Reformulated.B.Qk29.WtGe pi r (∑ i ∈ s, wt i) (∏ i ∈ s, F i) := by
  intro K inst ι _ pi hpi r α s wt F h
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UpperTheory.Reformulated.B.Qk29.wtGe_one hpi r
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact UpperTheory.Reformulated.B.Qk29.wtGe_mul hpi (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
