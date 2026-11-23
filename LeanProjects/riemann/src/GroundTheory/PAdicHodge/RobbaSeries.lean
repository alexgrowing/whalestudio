import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology

namespace Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

def ConvergesAt (a : ℤ → K) (ρ : ℝ) : Prop :=
  Tendsto (fun n : ℤ => ‖a n‖ * ρ ^ n) cofinite (𝓝 0)

def cmul (a b : ℤ → K) : ℤ → K := fun n => ∑' i, a i * b (n - i)

def gaussNorm (a : ℤ → K) (ρ : ℝ) : ℝ := ⨆ n, ‖a n‖ * ρ ^ n

def domSet (a : ℤ → K) (ρ : ℝ) : Set ℤ := {n | ‖a n‖ * ρ ^ n = gaussNorm a ρ}

def lowIndex (a : ℤ → K) (ρ : ℝ) : ℤ := sInf (domSet a ρ)

def highIndex (a : ℤ → K) (ρ : ℝ) : ℤ := sSup (domSet a ρ)

variable {a b c : ℤ → K} {ρ : ℝ}

section Basic

theorem ConvergesAt.bddAbove (h : ConvergesAt a ρ) :
    BddAbove (Set.range fun n : ℤ => ‖a n‖ * ρ ^ n) :=
  h.bddAbove_range_of_cofinite

theorem ConvergesAt.le_gaussNorm (h : ConvergesAt a ρ) (n : ℤ) :
    ‖a n‖ * ρ ^ n ≤ gaussNorm a ρ :=
  le_ciSup h.bddAbove n

theorem gaussNorm_le {C : ℝ} (h : ∀ n, ‖a n‖ * ρ ^ n ≤ C) : gaussNorm a ρ ≤ C :=
  ciSup_le h

theorem gaussNorm_nonneg (hρ : 0 < ρ) : 0 ≤ gaussNorm a ρ :=
  Real.iSup_nonneg fun n => by positivity

theorem ConvergesAt.finite_le (h : ConvergesAt a ρ) {ε : ℝ} (hε : 0 < ε) :
    {n | ε ≤ ‖a n‖ * ρ ^ n}.Finite := by
  have := Filter.eventually_cofinite.1 (h.eventually (gt_mem_nhds hε))
  simpa only [not_lt] using this

theorem convergesAt_zero : ConvergesAt (0 : ℤ → K) ρ := by
  simp [ConvergesAt]

theorem ConvergesAt.add (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    ConvergesAt (a + b) ρ := by
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) (by simpa using Tendsto.add ha hb)
  simp only [Pi.add_apply]
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)

theorem ConvergesAt.neg (ha : ConvergesAt a ρ) : ConvergesAt (-a) ρ := by
  simpa [ConvergesAt] using ha

theorem ConvergesAt.sub (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    ConvergesAt (a - b) ρ := by
  simpa [sub_eq_add_neg] using ha.add hρ hb.neg

theorem ConvergesAt.smul (k : K) (ha : ConvergesAt a ρ) : ConvergesAt (k • a) ρ := by
  simpa [ConvergesAt, norm_mul, mul_assoc] using ha.const_mul ‖k‖

theorem ConvergesAt.of_le_of_le {ρ₁ ρ₂ : ℝ} (h₁ : ConvergesAt a ρ₁) (h₂ : ConvergesAt a ρ₂)
    (hρ₁ : 0 < ρ₁) (h1 : ρ₁ ≤ ρ) (h2 : ρ ≤ ρ₂) : ConvergesAt a ρ := by
  have hρ : 0 < ρ := hρ₁.trans_le h1
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) (by simpa using Tendsto.add h₁ h₂)
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rcases le_total 0 n with hn | hn
  · have := zpow_le_zpow_left₀ hn hρ.le h2
    have : 0 ≤ ρ₁ ^ n := by positivity
    linarith
  · have h3 : ρ ^ n ≤ ρ₁ ^ n := by
      rw [show ρ ^ n = (ρ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv],
        show ρ₁ ^ n = (ρ₁ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]
      exact inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (neg_nonneg.2 hn) hρ₁.le h1)
    have hρ₂ : 0 < ρ₂ := by linarith
    have : 0 ≤ ρ₂ ^ n := by positivity
    linarith

end Basic

section Product

theorem norm_mul_term (hρ : ρ ≠ 0) (n i : ℤ) :
    ‖a i * b (n - i)‖ = (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)) / ρ ^ n := by
  rw [norm_mul, eq_div_iff (zpow_ne_zero _ hρ)]
  have : ρ ^ n = ρ ^ i * ρ ^ (n - i) := by rw [← zpow_add₀ hρ]; congr 1; ring
  rw [this]; ring

theorem tendsto_weight_prod (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    Tendsto (fun p : ℤ × ℤ => (‖a p.1‖ * ρ ^ p.1) * (‖b p.2‖ * ρ ^ p.2)) cofinite (𝓝 0) :=
  tendsto_mul_cofinite_nhds_zero ha hb

theorem ConvergesAt.tendsto_term (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (n : ℤ) : Tendsto (fun i => a i * b (n - i)) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hinj : Function.Injective (fun i : ℤ => (i, n - i)) := fun i j h => (Prod.ext_iff.1 h).1
  have := ((tendsto_weight_prod ha hb).comp hinj.tendsto_cofinite).div_const (ρ ^ n)
  rw [zero_div] at this
  refine this.congr fun i => ?_
  simp only [Function.comp, norm_mul_term (a := a) (b := b) hρ.ne' n i]

theorem ConvergesAt.summable_term [CompleteSpace K] (hρ : 0 < ρ) (ha : ConvergesAt a ρ)
    (hb : ConvergesAt b ρ) (n : ℤ) : Summable (fun i => a i * b (n - i)) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (ha.tendsto_term hρ hb n)

theorem norm_cmul_mul_zpow_le (hρ : 0 < ρ) {n : ℤ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)) ≤ C) :
    ‖cmul a b n‖ * ρ ^ n ≤ C := by
  have hρn : 0 < ρ ^ n := zpow_pos hρ n
  rw [← le_div_iff₀ hρn]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (div_nonneg hC hρn.le) fun i => ?_
  rw [norm_mul_term hρ.ne' n i]
  exact div_le_div_of_nonneg_right (h i) hρn.le

theorem ConvergesAt.cmul (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    ConvergesAt (cmul a b) ρ := by
  have hw := tendsto_weight_prod ha hb
  refine tendsto_order.2 ⟨fun x hx => Eventually.of_forall fun n =>
    lt_of_lt_of_le hx (by positivity), fun ε hε => ?_⟩
  have hS : {p : ℤ × ℤ | ε / 2 ≤ (‖a p.1‖ * ρ ^ p.1) * (‖b p.2‖ * ρ ^ p.2)}.Finite := by
    have := Filter.eventually_cofinite.1 (hw.eventually (gt_mem_nhds (half_pos hε)))
    simpa only [not_lt] using this
  refine Filter.eventually_cofinite.2 ((hS.image fun p => p.1 + p.2).subset fun n hn => ?_)
  simp only [Set.mem_setOf_eq, not_lt] at hn
  by_contra hcon
  have : ‖Laurent.cmul a b n‖ * ρ ^ n ≤ ε / 2 := norm_cmul_mul_zpow_le hρ (by positivity) fun i => by
    by_contra h'
    exact hcon ⟨(i, n - i), (not_le.1 h').le, by simp⟩
  linarith

variable [CompleteSpace K]

theorem cmul_comm (a b : ℤ → K) : cmul a b = cmul b a := by
  funext n
  unfold cmul
  rw [← (Equiv.subLeft n).tsum_eq (fun i => a i * b (n - i))]
  simp [Equiv.subLeft_apply, mul_comm]

theorem cmul_single_zero_one (a : ℤ → K) : cmul a (Pi.single 0 1) = a := by
  funext n
  unfold cmul
  rw [tsum_eq_single n fun i hi => by simp [Pi.single_apply, sub_eq_zero, Ne.symm hi]]
  simp

theorem single_zero_one_cmul (a : ℤ → K) : cmul (Pi.single 0 1) a = a := by
  rw [cmul_comm, cmul_single_zero_one]

theorem cmul_add (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (hc : ConvergesAt c ρ) : cmul a (b + c) = cmul a b + cmul a c := by
  funext n
  simp only [cmul, Pi.add_apply, mul_add]
  exact (ha.summable_term hρ hb n).tsum_add (ha.summable_term hρ hc n)

theorem add_cmul (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (hc : ConvergesAt c ρ) : cmul (a + b) c = cmul a c + cmul b c := by
  rw [cmul_comm, cmul_add hρ hc ha hb, cmul_comm c, cmul_comm c]

theorem cmul_zero (a : ℤ → K) : cmul a 0 = 0 := by
  funext n; simp [cmul]

theorem zero_cmul (a : ℤ → K) : cmul 0 a = 0 := by
  funext n; simp [cmul]

theorem cmul_smul (k : K) (a b : ℤ → K) : cmul a (k • b) = k • cmul a b := by
  funext n
  simp only [cmul, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1; funext i; ring

theorem smul_cmul (k : K) (a b : ℤ → K) : cmul (k • a) b = k • cmul a b := by
  rw [cmul_comm, cmul_smul, cmul_comm]

theorem cmul_neg (a b : ℤ → K) : cmul a (-b) = -cmul a b := by
  have := cmul_smul (-1 : K) a b
  simpa using this

theorem cmul_assoc (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ)
    (hc : ConvergesAt c ρ) : cmul (cmul a b) c = cmul a (cmul b c) := by
  funext n
  simp only [cmul]
  have h1 : ∀ j, (∑' i, a i * b (j - i)) * c (n - j) = ∑' i, a i * b (j - i) * c (n - j) :=
    fun j => tsum_mul_right.symm
  have h2 : ∀ i, a i * ∑' k, b k * c (n - i - k) = ∑' j, a i * b (j - i) * c (n - j) := by
    intro i
    rw [← tsum_mul_left, ← (Equiv.subRight i).tsum_eq (fun k => a i * (b k * c (n - i - k)))]
    congr 1; funext j
    simp only [Equiv.subRight_apply]
    rw [show n - i - (j - i) = n - j by ring, mul_assoc]
  simp_rw [h1, h2]
  have hsum : Summable (Function.uncurry fun i j => a i * b (j - i) * c (n - j)) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h3 := tendsto_mul_cofinite_nhds_zero ha (tendsto_weight_prod hb hc)
    have hinj : Function.Injective (fun p : ℤ × ℤ => (p.1, (p.2 - p.1, n - p.2))) := by
      intro p q h
      simp only [Prod.mk.injEq] at h
      ext <;> omega
    have := (h3.comp hinj.tendsto_cofinite).div_const (ρ ^ n)
    rw [zero_div] at this
    refine this.congr fun ⟨i, j⟩ => ?_
    simp only [Function.comp, Function.uncurry_apply_pair, norm_mul]
    have hρ' := hρ.ne'
    have : ρ ^ n = ρ ^ i * ρ ^ (j - i) * ρ ^ (n - j) := by
      rw [← zpow_add₀ hρ', ← zpow_add₀ hρ']; congr 1; ring
    rw [this]
    field_simp
  exact hsum.tsum_comm

end Product

section Dominant

theorem norm_tsum_lt {ι : Type*} {f : ι → K} (hf : Tendsto f cofinite (𝓝 0)) {M : ℝ}
    (hM : 0 < M) (h : ∀ i, ‖f i‖ < M) : ‖∑' i, f i‖ < M := by
  classical
  have hS : {i | M / 2 ≤ ‖f i‖}.Finite := by
    have := Filter.eventually_cofinite.1
      ((tendsto_zero_iff_norm_tendsto_zero.1 hf).eventually (gt_mem_nhds (half_pos hM)))
    simpa only [not_lt] using this
  set s := insert (M / 2) (hS.toFinset.image fun i => ‖f i‖)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  have hlt : s.max' hs < M := (Finset.max'_lt_iff s hs).2 fun y hy => by
    rcases Finset.mem_insert.1 hy with rfl | hy
    · linarith
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy; exact h i
  refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg ?_ fun i => ?_) hlt
  · exact (by linarith : (0:ℝ) ≤ M / 2).trans (s.le_max' _ (Finset.mem_insert_self _ _))
  · by_cases hi : M / 2 ≤ ‖f i‖
    · exact s.le_max' _ (Finset.mem_insert_of_mem
        (Finset.mem_image.2 ⟨i, by simpa [Set.Finite.mem_toFinset] using hi, rfl⟩))
    · exact (not_le.1 hi).le.trans (s.le_max' _ (Finset.mem_insert_self _ _))

theorem norm_tsum_eq_of_dominant [CompleteSpace K] {ι : Type*} {f : ι → K}
    (hf : Tendsto f cofinite (𝓝 0)) (i₀ : ι) (h0 : f i₀ ≠ 0)
    (h : ∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) : ‖∑' i, f i‖ = ‖f i₀‖ := by
  classical
  have hg : Tendsto (fun i => if i = i₀ then 0 else f i) cofinite (𝓝 0) := by
    refine hf.congr' ?_
    filter_upwards [(Set.finite_singleton i₀).compl_mem_cofinite] with i hi
    simp [show i ≠ i₀ from hi]
  have hsum : Summable (Function.update f i₀ 0) :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (by convert hg using 1; funext i; simp [Function.update_apply])
  rw [hsum.tsum_eq_add_tsum_ite' i₀]
  have hlt : ‖∑' i, (if i = i₀ then 0 else f i)‖ < ‖f i₀‖ :=
    norm_tsum_lt hg (norm_pos_iff.2 h0) fun i => by
      by_cases hi : i = i₀
      · simp [hi, h0]
      · simpa [hi] using h i hi
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

section Attained

variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha

theorem ConvergesAt.exists_eq_gaussNorm : ∃ n, ‖a n‖ * ρ ^ n = gaussNorm a ρ := by
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 ha
  have hε : 0 < ‖a n0‖ * ρ ^ n0 := by have := norm_pos_iff.2 hn0; positivity
  set S := (h.finite_le hε).toFinset
  have hn0S : n0 ∈ S := by simp [S]
  obtain ⟨m, hmS, hm⟩ := S.exists_max_image (fun n => ‖a n‖ * ρ ^ n) ⟨n0, hn0S⟩
  refine ⟨m, le_antisymm (h.le_gaussNorm m) (gaussNorm_le fun n => ?_)⟩
  by_cases hn : n ∈ S
  · exact hm n hn
  · simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hn
    exact hn.le.trans (hm n0 hn0S)

theorem gaussNorm_pos : 0 < gaussNorm a ρ := by
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 ha
  have := norm_pos_iff.2 hn0
  exact lt_of_lt_of_le (by positivity) (h.le_gaussNorm n0)

theorem domSet_finite : (domSet a ρ).Finite :=
  (h.finite_le (gaussNorm_pos hρ h ha)).subset fun n hn => le_of_eq (Eq.symm hn)

theorem domSet_nonempty : (domSet a ρ).Nonempty :=
  h.exists_eq_gaussNorm hρ ha

theorem lowIndex_mem : lowIndex a ρ ∈ domSet a ρ :=
  Int.csInf_mem (domSet_nonempty hρ h ha) (domSet_finite hρ h ha).bddBelow

theorem highIndex_mem : highIndex a ρ ∈ domSet a ρ :=
  Int.csSup_mem (domSet_nonempty hρ h ha) (domSet_finite hρ h ha).bddAbove

theorem lowIndex_le {n : ℤ} (hn : n ∈ domSet a ρ) : lowIndex a ρ ≤ n :=
  csInf_le (domSet_finite hρ h ha).bddBelow hn

theorem le_highIndex {n : ℤ} (hn : n ∈ domSet a ρ) : n ≤ highIndex a ρ :=
  le_csSup (domSet_finite hρ h ha).bddAbove hn

theorem lowIndex_le_highIndex : lowIndex a ρ ≤ highIndex a ρ :=
  lowIndex_le hρ h ha (highIndex_mem hρ h ha)

theorem weight_lt_of_lt_lowIndex {n : ℤ} (hn : n < lowIndex a ρ) :
    ‖a n‖ * ρ ^ n < gaussNorm a ρ :=
  lt_of_le_of_ne (h.le_gaussNorm n) fun heq => absurd (lowIndex_le hρ h ha heq) (not_le.2 hn)

theorem weight_lt_of_highIndex_lt {n : ℤ} (hn : highIndex a ρ < n) :
    ‖a n‖ * ρ ^ n < gaussNorm a ρ :=
  lt_of_le_of_ne (h.le_gaussNorm n) fun heq => absurd (le_highIndex hρ h ha heq) (not_le.2 hn)

theorem ne_zero_of_mem_domSet {n : ℤ} (hn : n ∈ domSet a ρ) : a n ≠ 0 := by
  intro h0
  have := gaussNorm_pos hρ h ha
  simp only [domSet, Set.mem_setOf_eq, h0, norm_zero, zero_mul] at hn
  linarith

end Attained

section Multiplicative

variable [CompleteSpace K]

private theorem prod_lt_left {x y X Y : ℝ} (hx0 : 0 ≤ x) (hx : x < X) (hy : y ≤ Y) (hY : 0 < Y) :
    x * y < X * Y :=
  calc x * y ≤ x * Y := mul_le_mul_of_nonneg_left hy hx0
    _ < X * Y := mul_lt_mul_of_pos_right hx hY

private theorem prod_lt_right {x y X Y : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ X) (hX : 0 < X) (hy0 : 0 ≤ y)
    (hy : y < Y) :
    x * y < X * Y := by
  rw [mul_comm x, mul_comm X]
  calc y * x ≤ y * X := mul_le_mul_of_nonneg_left hx (by linarith [hy0])
    _ < Y * X := mul_lt_mul_of_pos_right hy hX

theorem cmul_weight_lt (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) {n : ℤ}
    {M : ℝ} (hM : 0 < M) (hlt : ∀ i, (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)) < M) :
    ‖cmul a b n‖ * ρ ^ n < M := by
  have hρn : 0 < ρ ^ n := zpow_pos hρ n
  rw [← lt_div_iff₀ hρn]
  refine norm_tsum_lt (ha.tendsto_term hρ hb n) (div_pos hM hρn) fun i => ?_
  rw [norm_mul_term hρ.ne' n i]
  exact div_lt_div_of_pos_right (hlt i) hρn

theorem cmul_weight_eq (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) {n i₀ : ℤ}
    {M : ℝ} (hM : 0 < M) (heq : (‖a i₀‖ * ρ ^ i₀) * (‖b (n - i₀)‖ * ρ ^ (n - i₀)) = M)
    (hlt : ∀ i, i ≠ i₀ → (‖a i‖ * ρ ^ i) * (‖b (n - i)‖ * ρ ^ (n - i)) < M) :
    ‖cmul a b n‖ * ρ ^ n = M := by
  have hρn : 0 < ρ ^ n := zpow_pos hρ n
  rw [← eq_div_iff hρn.ne']
  have h0 : a i₀ * b (n - i₀) ≠ 0 := by
    intro h0
    have := norm_mul_term (a := a) (b := b) hρ.ne' n i₀
    rw [h0, norm_zero, heq] at this
    exact (div_pos hM hρn).ne' this.symm
  unfold cmul
  rw [norm_tsum_eq_of_dominant (ha.tendsto_term hρ hb n) i₀ h0 fun i hi => ?_,
    norm_mul_term hρ.ne' n i₀, heq]
  rw [norm_mul_term hρ.ne' n i, norm_mul_term hρ.ne' n i₀, heq]
  exact div_lt_div_of_pos_right (hlt i hi) hρn

variable (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
include hρ ha hb ha0 hb0

private theorem low_facts :
    ‖cmul a b (lowIndex a ρ + lowIndex b ρ)‖ * ρ ^ (lowIndex a ρ + lowIndex b ρ) =
      gaussNorm a ρ * gaussNorm b ρ ∧
    ∀ n < lowIndex a ρ + lowIndex b ρ, ‖cmul a b n‖ * ρ ^ n < gaussNorm a ρ * gaussNorm b ρ := by
  have hA := gaussNorm_pos hρ ha ha0
  have hB := gaussNorm_pos hρ hb hb0
  have hM := mul_pos hA hB
  set i₀ := lowIndex a ρ
  set j₀ := lowIndex b ρ
  have wa : ∀ i, 0 ≤ ‖a i‖ * ρ ^ i := fun i => by positivity
  have wb : ∀ i, 0 ≤ ‖b i‖ * ρ ^ i := fun i => by positivity
  refine ⟨cmul_weight_eq (i₀ := i₀) hρ ha hb hM ?_ fun i hi => ?_, fun n hn =>
    cmul_weight_lt hρ ha hb hM fun i => ?_⟩
  · rw [show i₀ + j₀ - i₀ = j₀ by ring,
      show ‖a i₀‖ * ρ ^ i₀ = gaussNorm a ρ from lowIndex_mem hρ ha ha0,
      show ‖b j₀‖ * ρ ^ j₀ = gaussNorm b ρ from lowIndex_mem hρ hb hb0]
  · rcases lt_or_gt_of_ne hi with hi | hi
    · exact prod_lt_left (wa _) (weight_lt_of_lt_lowIndex hρ ha ha0 hi) (hb.le_gaussNorm _) hB
    · exact prod_lt_right (wa _) (ha.le_gaussNorm _) hA (wb _)
        (weight_lt_of_lt_lowIndex hρ hb hb0 (by omega))
  · rcases lt_or_ge i i₀ with hi | hi
    · exact prod_lt_left (wa _) (weight_lt_of_lt_lowIndex hρ ha ha0 hi) (hb.le_gaussNorm _) hB
    · exact prod_lt_right (wa _) (ha.le_gaussNorm _) hA (wb _)
        (weight_lt_of_lt_lowIndex hρ hb hb0 (by omega))

private theorem high_facts :
    ‖cmul a b (highIndex a ρ + highIndex b ρ)‖ * ρ ^ (highIndex a ρ + highIndex b ρ) =
      gaussNorm a ρ * gaussNorm b ρ ∧
    ∀ n > highIndex a ρ + highIndex b ρ,
      ‖cmul a b n‖ * ρ ^ n < gaussNorm a ρ * gaussNorm b ρ := by
  have hA := gaussNorm_pos hρ ha ha0
  have hB := gaussNorm_pos hρ hb hb0
  have hM := mul_pos hA hB
  set i₀ := highIndex a ρ
  set j₀ := highIndex b ρ
  have wa : ∀ i, 0 ≤ ‖a i‖ * ρ ^ i := fun i => by positivity
  have wb : ∀ i, 0 ≤ ‖b i‖ * ρ ^ i := fun i => by positivity
  refine ⟨cmul_weight_eq (i₀ := i₀) hρ ha hb hM ?_ fun i hi => ?_, fun n hn =>
    cmul_weight_lt hρ ha hb hM fun i => ?_⟩
  · rw [show i₀ + j₀ - i₀ = j₀ by ring,
      show ‖a i₀‖ * ρ ^ i₀ = gaussNorm a ρ from highIndex_mem hρ ha ha0,
      show ‖b j₀‖ * ρ ^ j₀ = gaussNorm b ρ from highIndex_mem hρ hb hb0]
  · rcases lt_or_gt_of_ne hi with hi | hi
    · exact prod_lt_right (wa _) (ha.le_gaussNorm _) hA (wb _)
        (weight_lt_of_highIndex_lt hρ hb hb0 (by omega))
    · exact prod_lt_left (wa _) (weight_lt_of_highIndex_lt hρ ha ha0 hi) (hb.le_gaussNorm _) hB
  · rcases lt_or_ge i₀ i with hi | hi
    · exact prod_lt_left (wa _) (weight_lt_of_highIndex_lt hρ ha ha0 hi) (hb.le_gaussNorm _) hB
    · exact prod_lt_right (wa _) (ha.le_gaussNorm _) hA (wb _)
        (weight_lt_of_highIndex_lt hρ hb hb0 (by omega))

theorem gaussNorm_cmul : gaussNorm (cmul a b) ρ = gaussNorm a ρ * gaussNorm b ρ := by
  refine le_antisymm (gaussNorm_le fun n => norm_cmul_mul_zpow_le hρ
    (mul_nonneg (gaussNorm_nonneg hρ) (gaussNorm_nonneg hρ)) fun i =>
      mul_le_mul (ha.le_gaussNorm i) (hb.le_gaussNorm _) (by positivity) (gaussNorm_nonneg hρ)) ?_
  rw [← (low_facts hρ ha hb ha0 hb0).1]
  exact (ha.cmul hρ hb).le_gaussNorm _

theorem cmul_ne_zero : cmul a b ≠ 0 := by
  intro h0
  have h1 := (low_facts hρ ha hb ha0 hb0).1
  rw [h0] at h1
  have := mul_pos (gaussNorm_pos hρ ha ha0) (gaussNorm_pos hρ hb hb0)
  simp only [Pi.zero_apply, norm_zero, zero_mul] at h1
  linarith

theorem lowIndex_cmul : lowIndex (cmul a b) ρ = lowIndex a ρ + lowIndex b ρ := by
  have hc := ha.cmul hρ hb
  have hc0 := cmul_ne_zero hρ ha hb ha0 hb0
  have hmem : lowIndex a ρ + lowIndex b ρ ∈ domSet (cmul a b) ρ := by
    simp only [domSet, Set.mem_setOf_eq, gaussNorm_cmul hρ ha hb ha0 hb0]
    exact (low_facts hρ ha hb ha0 hb0).1
  refine le_antisymm (lowIndex_le hρ hc hc0 hmem) (not_lt.1 fun hlt => ?_)
  have h1 := (low_facts hρ ha hb ha0 hb0).2 _ hlt
  have h2 := lowIndex_mem hρ hc hc0
  simp only [domSet, Set.mem_setOf_eq, gaussNorm_cmul hρ ha hb ha0 hb0] at h2
  linarith

theorem highIndex_cmul : highIndex (cmul a b) ρ = highIndex a ρ + highIndex b ρ := by
  have hc := ha.cmul hρ hb
  have hc0 := cmul_ne_zero hρ ha hb ha0 hb0
  have hmem : highIndex a ρ + highIndex b ρ ∈ domSet (cmul a b) ρ := by
    simp only [domSet, Set.mem_setOf_eq, gaussNorm_cmul hρ ha hb ha0 hb0]
    exact (high_facts hρ ha hb ha0 hb0).1
  refine le_antisymm (not_lt.1 fun hlt => ?_) (le_highIndex hρ hc hc0 hmem)
  have h1 := (high_facts hρ ha hb ha0 hb0).2 _ hlt
  have h2 := highIndex_mem hρ hc hc0
  simp only [domSet, Set.mem_setOf_eq, gaussNorm_cmul hρ ha hb ha0 hb0] at h2
  linarith

end Multiplicative

theorem le_of_mem_domSet {ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') (h : ConvergesAt a ρ)
    (h' : ConvergesAt a ρ') (ha : a ≠ 0) {n m : ℤ} (hn : n ∈ domSet a ρ)
    (hm : m ∈ domSet a ρ') : n ≤ m := by
  have hρ' : 0 < ρ' := hρ.trans hρρ'
  by_contra hlt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = m + (k + 1 : ℕ) := ⟨(n - m - 1).toNat, by omega⟩
  have hA : 0 < ‖a n‖ := norm_pos_iff.2 (ne_zero_of_mem_domSet hρ h ha hn)
  have hB : 0 < ‖a m‖ := norm_pos_iff.2 (ne_zero_of_mem_domSet hρ' h' ha hm)
  have e1 : ‖a m‖ * ρ ^ m ≤ ‖a n‖ * ρ ^ n := by rw [hn]; exact h.le_gaussNorm m
  have e2 : ‖a n‖ * ρ' ^ n ≤ ‖a m‖ * ρ' ^ m := by rw [hm]; exact h'.le_gaussNorm n
  rw [show ρ ^ n = ρ ^ m * ρ ^ (k + 1) by rw [hk, zpow_add₀ hρ.ne', zpow_natCast]] at e1
  rw [show ρ' ^ n = ρ' ^ m * ρ' ^ (k + 1) by rw [hk, zpow_add₀ hρ'.ne', zpow_natCast]] at e2
  have hm1 : 0 < ρ ^ m := zpow_pos hρ m
  have hm2 : 0 < ρ' ^ m := zpow_pos hρ' m
  have f1 : ‖a m‖ ≤ ‖a n‖ * ρ ^ (k + 1) := by
    have : ‖a m‖ * ρ ^ m ≤ (‖a n‖ * ρ ^ (k + 1)) * ρ ^ m := by linarith
    exact le_of_mul_le_mul_right this hm1
  have f2 : ‖a n‖ * ρ' ^ (k + 1) ≤ ‖a m‖ := by
    have : (‖a n‖ * ρ' ^ (k + 1)) * ρ' ^ m ≤ ‖a m‖ * ρ' ^ m := by linarith
    exact le_of_mul_le_mul_right this hm2
  have f3 : ρ ^ (k + 1) < ρ' ^ (k + 1) := pow_lt_pow_left₀ hρρ' hρ.le (by omega)
  have : ‖a n‖ * ρ ^ (k + 1) < ‖a n‖ * ρ' ^ (k + 1) := mul_lt_mul_of_pos_left f3 hA
  linarith

theorem highIndex_le_lowIndex {ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') (h : ConvergesAt a ρ)
    (h' : ConvergesAt a ρ') (ha : a ≠ 0) : highIndex a ρ ≤ lowIndex a ρ' :=
  le_of_mem_domSet hρ hρρ' h h' ha (highIndex_mem hρ h ha)
    (lowIndex_mem (hρ.trans hρρ') h' ha)

end Dominant

end Laurent

end GroundTheory.PAdicHodge
