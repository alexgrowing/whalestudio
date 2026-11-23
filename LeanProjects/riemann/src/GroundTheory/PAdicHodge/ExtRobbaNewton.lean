import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaComplete
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

section Seq

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] {a : ℤ → L} {α β : ℝ}

theorem weight_le_max_of_mem_Icc (hα : 0 < α) {σ : ℝ} (hσ : σ ∈ Set.Icc α β) (n : ℤ) :
    ‖a n‖ * σ ^ n ≤ max (‖a n‖ * α ^ n) (‖a n‖ * β ^ n) := by
  have hσ0 : 0 < σ := hα.trans_le hσ.1
  rcases le_total 0 n with hn | hn
  · exact le_max_of_le_right (mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ hn hσ0.le hσ.2)
      (norm_nonneg _))
  · have h3 : σ ^ n ≤ α ^ n := by
      rw [show σ ^ n = (σ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv],
        show α ^ n = (α ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]
      exact inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (neg_nonneg.2 hn) hα.le hσ.1)
    exact le_max_of_le_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))

theorem continuousOn_gaussNorm (hα : 0 < α) (hA : ConvergesAt a α) (hB : ConvergesAt a β)
    (ha : a ≠ 0) : ContinuousOn (gaussNorm a) (Set.Icc α β) := by
  classical
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 ha
  set ε0 := ‖a n0‖ * min (α ^ n0) (β ^ n0) with hε0
  by_cases hαβ : α ≤ β
  swap
  · rw [Set.Icc_eq_empty hαβ]; exact continuousOn_empty _
  have hβ : 0 < β := hα.trans_le hαβ
  have hε0pos : 0 < ε0 := mul_pos (norm_pos_iff.2 hn0) (lt_min (zpow_pos hα _) (zpow_pos hβ _))
  have hfin : {n | ε0 ≤ ‖a n‖ * α ^ n ∨ ε0 ≤ ‖a n‖ * β ^ n}.Finite :=
    ((hA.finite_le hε0pos).union (hB.finite_le hε0pos)).subset fun n hn => hn
  set S := hfin.toFinset
  have hn0S : n0 ∈ S := by
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    left
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (norm_nonneg _)
  have hne : S.Nonempty := ⟨n0, hn0S⟩
  have hlow : ∀ σ ∈ Set.Icc α β, ε0 ≤ ‖a n0‖ * σ ^ n0 := by
    intro σ hσ
    have hσ0 : 0 < σ := hα.trans_le hσ.1
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rcases le_total 0 n0 with hn | hn
    · exact (min_le_left _ _).trans (zpow_le_zpow_left₀ hn hα.le hσ.1)
    · refine (min_le_right _ _).trans ?_
      rw [show σ ^ n0 = (σ ^ (-n0))⁻¹ by rw [zpow_neg, inv_inv],
        show β ^ n0 = (β ^ (-n0))⁻¹ by rw [zpow_neg, inv_inv]]
      exact inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (neg_nonneg.2 hn) hσ0.le hσ.2)
  have heq : Set.EqOn (gaussNorm a) (fun σ => S.sup' hne fun n => ‖a n‖ * σ ^ n) (Set.Icc α β) := by
    intro σ hσ
    have hc : ConvergesAt a σ := hA.of_le_of_le hB hα hσ.1 hσ.2
    refine le_antisymm (gaussNorm_le fun n => ?_) (Finset.sup'_le _ _ fun n _ => hc.le_gaussNorm n)
    by_cases hn : n ∈ S
    · exact Finset.le_sup' (fun n => ‖a n‖ * σ ^ n) hn
    · simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_le] at hn
      calc ‖a n‖ * σ ^ n ≤ max (‖a n‖ * α ^ n) (‖a n‖ * β ^ n) :=
            weight_le_max_of_mem_Icc hα hσ n
        _ ≤ ε0 := (max_lt hn.1 hn.2).le
        _ ≤ ‖a n0‖ * σ ^ n0 := hlow σ hσ
        _ ≤ _ := Finset.le_sup' (fun n => ‖a n‖ * σ ^ n) hn0S
  refine ContinuousOn.congr ?_ heq
  exact ContinuousOn.finset_sup'_apply hne fun n _ =>
    continuousOn_const.mul ((continuousOn_zpow₀ n).mono fun σ hσ =>
      Set.mem_compl_singleton_iff.2 (hα.trans_le hσ.1).ne')

theorem exists_right_nbhd {ρ ρ₁ : ℝ} (hρ0 : 0 < ρ) (hρρ₁ : ρ < ρ₁) (hA : ConvergesAt a ρ)
    (hB : ConvergesAt a ρ₁) (ha : a ≠ 0) :
    ∃ δ > 0, ρ + δ ≤ ρ₁ ∧ ∀ ρ' ∈ Set.Ioo ρ (ρ + δ),
      lowIndex a ρ' = highIndex a ρ ∧ highIndex a ρ' = highIndex a ρ := by
  classical
  have hfin := breaks_finite hρ0 hρρ₁.le hA hB ha
  set F := (hfin.toFinset.filter (ρ < ·)).image (· - ρ)
  set δ := (insert (ρ₁ - ρ) F).min' (Finset.insert_nonempty _ _)
  have hδpos : 0 < δ := by
    rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · linarith
    · obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hy
      simp only [Finset.mem_filter] at hσ
      linarith [hσ.2]
  have hδle : δ ≤ ρ₁ - ρ := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  refine ⟨δ, hδpos, by linarith, fun ρ' hρ' => ?_⟩
  have hρ'0 : 0 < ρ' := hρ0.trans hρ'.1
  have hc : ConvergesAt a ρ' := hA.of_le_of_le hB hρ0 hρ'.1.le (by linarith [hρ'.2])

  have hnob : ∀ σ ∈ Set.Ioo ρ (ρ + δ), ¬ (lowIndex a σ < highIndex a σ) := by
    intro σ hσ hbr
    have hmem : σ ∈ hfin.toFinset := by
      simp only [Set.Finite.mem_toFinset, breaks, Set.mem_setOf_eq]
      exact ⟨⟨hσ.1.le, by linarith [hσ.2]⟩, hbr⟩
    have : δ ≤ σ - ρ := Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨σ, Finset.mem_filter.2 ⟨hmem, hσ.1⟩, rfl⟩))
    linarith [hσ.2]
  have h1 := highIndex_le_lowIndex hρ0 hρ'.1 hA hc ha
  have h2 := lowIndex_le_highIndex hρ'0 hc ha
  have h3 : lowIndex a ρ' = highIndex a ρ' := le_antisymm h2 (not_lt.1 (hnob ρ' hρ'))
  have h4 : lowIndex a ρ' ≤ highIndex a ρ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨σ, hσ, hσ1, hσ2⟩ := exists_break hρ0 hρ'.1.le hA hc ha (n := highIndex a ρ)
      (lowIndex_le_highIndex hρ0 hA ha) (by omega)
    rcases hσ.1.lt_or_eq with hlt | heq
    · exact hnob σ ⟨hlt, by linarith [hσ.2, hρ'.2]⟩ (by omega)
    · subst heq; omega
  exact ⟨le_antisymm h4 h1, by omega⟩

end Seq

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}

theorem lowIndex_zcoeff_add_of_lt {x y : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hx : ConvergesAt (T.zcoeff x) ρ) (hy : ConvergesAt (T.zcoeff y) ρ) (hx0 : x ≠ 0)
    (hlt : gaussNorm (T.zcoeff y) ρ < gaussNorm (T.zcoeff x) ρ) :
    gaussNorm (T.zcoeff (x + y)) ρ = gaussNorm (T.zcoeff x) ρ ∧
      lowIndex (T.zcoeff (x + y)) ρ = lowIndex (T.zcoeff x) ρ := by
  have hx0' : T.zcoeff x ≠ 0 := fun h => hx0 ((T.zcoeff_eq_zero_iff x).1 h)
  set gx := gaussNorm (T.zcoeff x) ρ with hgxdef
  have hgx : 0 < gx := gaussNorm_pos hρ0 hx hx0'
  have hgy0 : 0 ≤ gaussNorm (T.zcoeff y) ρ := gaussNorm_nonneg hρ0
  have hi0 := lowIndex_mem hρ0 hx hx0'
  have hi0nn : 0 ≤ lowIndex (T.zcoeff x) ρ := by
    by_contra h
    push_neg at h
    exact ne_zero_of_mem_domSet hρ0 hx hx0' hi0 (T.zcoeff_of_neg x h)
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℕ, lowIndex (T.zcoeff x) ρ = k0 :=
    ⟨_, (Int.toNat_of_nonneg hi0nn).symm⟩
  have hwk0 : ‖T.coeff x k0‖ * ρ ^ (k0 : ℤ) = gx := by
    have := hi0; rw [hk0] at this
    simp only [domSet, Set.mem_setOf_eq, T.zcoeff_natCast] at this; exact this
  have hlt_x : ∀ i < k0, ‖T.coeff x i‖ * ρ ^ (i : ℤ) < gx := fun i hi => by
    have := weight_lt_of_lt_lowIndex hρ0 hx hx0' (n := i) (by rw [hk0]; exact_mod_cast hi)
    rwa [T.zcoeff_natCast] at this
  obtain ⟨gA, hgA, hgA0, hgA'⟩ := exists_lt_bound hgx hlt_x
  set β := max gA (gaussNorm (T.zcoeff y) ρ) with hβdef
  have hβ : β < gx := max_lt hgA hlt
  have hβ0 : 0 ≤ β := le_max_of_le_left hgA0

  have hbelow : ∀ m : ℕ, m < k0 → ‖T.coeff (x + y) m‖ * ρ ^ (m : ℤ) ≤ β := by
    intro m hm
    have := T.norm_zcoeff_add_le (x := x) (y := y) (n := m) (div_nonneg hβ0 (zpow_pos hρ0 _).le)
      (fun i hi => by
        rcases lt_or_ge i 0 with hi0 | hi0
        · rw [T.zcoeff_of_neg _ hi0, norm_zero]; exact div_nonneg hβ0 (zpow_pos hρ0 _).le
        · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
          rw [T.zcoeff_natCast]
          exact norm_le_div_of_weight hρ0 hρ1.le hi ((hgA' j (by omega)).trans (le_max_left _ _)))
      (fun i hi => norm_le_div_of_weight hρ0 hρ1.le hi ((hy.le_gaussNorm i).trans (le_max_right _ _)))
    rwa [T.zcoeff_natCast, le_div_iff₀ (zpow_pos hρ0 _)] at this
  have hxy := T.convergesAt_zcoeff_add hρ0 hρ1 hx hy
  have hle : gaussNorm (T.zcoeff (x + y)) ρ ≤ gx :=
    (T.gaussNorm_zcoeff_add_le hρ0 hρ1.le hx hy).trans (max_le le_rfl hlt.le)

  have hk : gx ≤ ‖T.coeff (x + y) k0‖ * ρ ^ (k0 : ℤ) := by
    by_contra hcon
    push_neg at hcon
    set β' := max β (‖T.coeff (x + y) k0‖ * ρ ^ (k0 : ℤ))
    have hβ' : β' < gx := max_lt hβ hcon
    have hβ'0 : 0 ≤ β' := le_max_of_le_left hβ0
    have h1 : ∀ i ≤ (k0 : ℤ), ‖T.zcoeff (x + y) i‖ ≤ β' / ρ ^ (k0 : ℤ) := by
      intro i hi
      rcases lt_or_ge i 0 with hi0 | hi0
      · rw [T.zcoeff_of_neg _ hi0, norm_zero]; exact div_nonneg hβ'0 (zpow_pos hρ0 _).le
      obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
      rw [T.zcoeff_natCast]
      rcases (show j < k0 ∨ j = k0 by omega) with hj | rfl
      · exact norm_le_div_of_weight hρ0 hρ1.le hi ((hbelow j hj).trans (le_max_left _ _))
      · exact norm_le_div_of_weight hρ0 hρ1.le le_rfl (le_max_right _ _)
    have h2 : ∀ i ≤ (k0 : ℤ), ‖T.zcoeff (-y) i‖ ≤ β' / ρ ^ (k0 : ℤ) := fun i hi =>
      T.norm_zcoeff_neg_le (div_nonneg hβ'0 (zpow_pos hρ0 _).le)
        (fun m hm => norm_le_div_of_weight hρ0 hρ1.le (hm.trans hi)
          ((hy.le_gaussNorm m).trans ((le_max_right _ _).trans (le_max_left _ _))))
    have := T.norm_zcoeff_add_le (n := (k0 : ℤ)) (div_nonneg hβ'0 (zpow_pos hρ0 _).le) h1 h2
    rw [add_neg_cancel_right, T.zcoeff_natCast, le_div_iff₀ (zpow_pos hρ0 _), hwk0] at this
    linarith
  have hg : gaussNorm (T.zcoeff (x + y)) ρ = gx :=
    le_antisymm hle (hk.trans (T.weight_natCast_le hxy k0))
  refine ⟨hg, ?_⟩
  have hxy0 : T.zcoeff (x + y) ≠ 0 := by
    intro h
    have := congrFun h (k0 : ℤ)
    rw [T.zcoeff_natCast, Pi.zero_apply] at this
    rw [this, norm_zero, zero_mul] at hk
    linarith
  have hmem : (k0 : ℤ) ∈ domSet (T.zcoeff (x + y)) ρ := by
    simp only [domSet, Set.mem_setOf_eq, T.zcoeff_natCast]
    exact le_antisymm (T.weight_natCast_le hxy k0) (hg ▸ hk)
  rw [hk0]
  refine le_antisymm (lowIndex_le hρ0 hxy hxy0 hmem) ?_
  by_contra hcon
  push_neg at hcon
  have hj := lowIndex_mem hρ0 hxy hxy0
  simp only [domSet, Set.mem_setOf_eq] at hj
  rcases lt_or_ge (lowIndex (T.zcoeff (x + y)) ρ) 0 with hj0 | hj0
  · rw [T.zcoeff_of_neg _ hj0, norm_zero, zero_mul, hg] at hj
    linarith
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hj0
    rw [hm, T.zcoeff_natCast, hg] at hj
    have hmk : m < k0 := by omega
    linarith [hbelow m hmk]

theorem lowIndex_coeffB_add_of_lt {b c : T.B} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hb : ConvergesAt (T.coeffB b) ρ) (hc : ConvergesAt (T.coeffB c) ρ) (hb0 : b ≠ 0)
    (hlt : gaussNorm (T.coeffB c) ρ < gaussNorm (T.coeffB b) ρ) :
    gaussNorm (T.coeffB (b + c)) ρ = gaussNorm (T.coeffB b) ρ ∧
      lowIndex (T.coeffB (b + c)) ρ = lowIndex (T.coeffB b) ρ := by
  obtain ⟨x, y, N, hx, hy⟩ := T.exists_common b c
  have hxy : (b + c) * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B (x + y) := by
    rw [add_mul, hx, hy, map_add]
  have hx0 : x ≠ 0 := by rintro rfl; exact hb0 (T.eq_zero_of_mul_pow (by rw [hx, map_zero]))
  have hx0' : T.zcoeff x ≠ 0 := fun h => hx0 ((T.zcoeff_eq_zero_iff x).1 h)
  rw [T.coeffB_eq hx, convergesAt_shift_iff hρ0] at hb
  rw [T.coeffB_eq hy, convergesAt_shift_iff hρ0] at hc
  rw [T.coeffB_eq hx, T.coeffB_eq hy, gaussNorm_shift hρ0, gaussNorm_shift hρ0] at hlt
  have hlt' := lt_of_mul_lt_mul_right hlt (zpow_pos hρ0 _).le
  obtain ⟨h1, h2⟩ := T.lowIndex_zcoeff_add_of_lt hρ0 hρ1 hb hc hx0 hlt'
  have hxy0 : T.zcoeff (x + y) ≠ 0 := by
    intro h
    have := gaussNorm_pos hρ0 hb hx0'
    rw [← h1, h] at this
    simp [gaussNorm] at this
  rw [T.coeffB_eq hxy, T.coeffB_eq hx, gaussNorm_shift hρ0, gaussNorm_shift hρ0, h1,
    lowIndex_shift hρ0 (T.convergesAt_zcoeff_add hρ0 hρ1 hb hc) hxy0, lowIndex_shift hρ0 hb hx0', h2]
  exact ⟨rfl, rfl⟩

variable {ρ0 : Set.Ioo (0 : ℝ) 1}

def normR (x : T.RobbaExt ρ0) (ρ : ℝ) : ℝ :=
  if h : 0 < ρ ∧ ρ ≤ ρ0 then T.extNorm ρ0 ⟨ρ, h⟩ x else 0

theorem normR_eq (x : T.RobbaExt ρ0) (ρ : Set.Ioc (0 : ℝ) ρ0) : T.normR x ρ = T.extNorm ρ0 ρ x := by
  unfold normR
  split_ifs with h
  · rfl
  · exact absurd ρ.2 h

theorem abs_extNorm_sub_le (ρ : Set.Ioc (0 : ℝ) ρ0) (x y : T.RobbaExt ρ0) :
    |T.extNorm ρ0 ρ x - T.extNorm ρ0 ρ y| ≤ T.extNorm ρ0 ρ (x - y) := by
  have h1 := T.extNorm_add_le ρ (x - y) y
  have h2 := T.extNorm_add_le ρ (y - x) x
  rw [sub_add_cancel] at h1
  rw [sub_add_cancel, extNorm_sub_comm] at h2
  have hn1 := T.extNorm_nonneg ρ (x - y)
  have hn2 := T.extNorm_nonneg ρ y
  have hn3 := T.extNorm_nonneg ρ x
  rw [abs_sub_le_iff]
  constructor
  · rcases le_total (T.extNorm ρ0 ρ (x - y)) (T.extNorm ρ0 ρ y) with h | h
    · rw [max_eq_right h] at h1; linarith
    · rw [max_eq_left h] at h1; linarith
  · rcases le_total (T.extNorm ρ0 ρ (x - y)) (T.extNorm ρ0 ρ x) with h | h
    · rw [max_eq_right h] at h2; linarith
    · rw [max_eq_left h] at h2; linarith

theorem exists_approx_two (x : T.RobbaExt ρ0) (a b : Set.Ioc (0 : ℝ) ρ0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : T.Econ ρ0, T.extNorm ρ0 a (x - c) < ε ∧ T.extNorm ρ0 b (x - c) < ε := by
  have hU : {y : T.RobbaExt ρ0 | T.extNorm ρ0 a (x - y) < ε ∧ T.extNorm ρ0 b (x - y) < ε} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact (isOpen_lt ((T.continuous_extNorm a).comp (continuous_const.sub continuous_id))
        continuous_const).inter (isOpen_lt ((T.continuous_extNorm b).comp
          (continuous_const.sub continuous_id)) continuous_const)
    · simp only [Set.mem_setOf_eq, sub_self, extNorm_zero]; exact ⟨hε, hε⟩
  obtain ⟨c, hc⟩ := Completion.denseRange_coe.mem_nhds hU
  exact ⟨c, hc⟩

theorem continuousOn_normR (x : T.RobbaExt ρ0) (a b : Set.Ioc (0 : ℝ) ρ0) :
    ContinuousOn (T.normR x) (Set.Icc (a : ℝ) b) := by
  choose c hc using fun n : ℕ => T.exists_approx_two x a b (ε := 1 / (n + 1)) Nat.one_div_pos_of_nat
  have hrad : ∀ σ ∈ Set.Icc (a : ℝ) b, 0 < σ ∧ σ ≤ ρ0 := fun σ hσ =>
    ⟨a.2.1.trans_le hσ.1, hσ.2.trans b.2.2⟩
  refine TendstoUniformlyOn.continuousOn (F := fun n σ => gaussNorm (T.coeffB (c n)) σ) ?_
    (Filter.Frequently.of_forall (f := atTop) fun n => ?_)
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with n hn σ hσ
    have hσr := hrad σ hσ
    rw [Real.dist_eq, T.normR_eq x ⟨σ, hσr⟩, ← T.extNorm_coe ⟨σ, hσr⟩ (c n)]
    refine (T.abs_extNorm_sub_le _ _ _).trans_lt ?_
    refine (T.extNorm_le_max a b ⟨σ, hσr⟩ hσ.1 hσ.2 _).trans_lt (max_lt ?_ ?_)
    · exact (hc n).1.trans_le ((Nat.one_div_le_one_div hn).trans hN.le)
    · exact (hc n).2.trans_le ((Nat.one_div_le_one_div hn).trans hN.le)
  · by_cases h0 : T.coeffB (c n) = 0
    · simp only [h0]
      have : gaussNorm (0 : ℤ → L) = fun _ => 0 := by funext σ; simp [gaussNorm]
      rw [this]; exact continuousOn_const
    · exact continuousOn_gaussNorm a.2.1 (T.convergesAt_rad ρ0 (c n) a)
        (T.convergesAt_rad ρ0 (c n) b) h0

theorem exists_approx_norm {x : T.RobbaExt ρ0} (hx : x ≠ 0) (a b : Set.Ioc (0 : ℝ) ρ0)
    (hab : (a : ℝ) ≤ b) :
    ∃ c : T.Econ ρ0, ∀ σ : Set.Ioc (0 : ℝ) ρ0, (a : ℝ) ≤ σ → (σ : ℝ) ≤ b →
      T.extNorm ρ0 σ (x - c) < T.extNorm ρ0 σ x := by
  obtain ⟨σm, hσm, hmin⟩ := (isCompact_Icc (a := (a : ℝ)) (b := b)).exists_isMinOn
    ⟨a, le_rfl, hab⟩ (T.continuousOn_normR x a b)
  have hσmr : 0 < σm ∧ σm ≤ ρ0 := ⟨a.2.1.trans_le hσm.1, hσm.2.trans b.2.2⟩
  have hm : 0 < T.normR x σm := by rw [T.normR_eq x ⟨σm, hσmr⟩]; exact T.extNorm_pos hx _
  obtain ⟨c, hc1, hc2⟩ := T.exists_approx_two x a b hm
  refine ⟨c, fun σ h1 h2 => ?_⟩
  refine (T.extNorm_le_max a b σ h1 h2 _).trans_lt ((max_lt hc1 hc2).trans_le ?_)
  have := hmin (show (σ : ℝ) ∈ Set.Icc (a : ℝ) b from ⟨h1, h2⟩)
  simp only [Set.mem_setOf_eq] at this
  rwa [T.normR_eq x σ] at this

theorem extNorm_eq_of_lt {x c : T.RobbaExt ρ0} {σ : Set.Ioc (0 : ℝ) ρ0}
    (h : T.extNorm ρ0 σ (x - c) < T.extNorm ρ0 σ x) : T.extNorm ρ0 σ c = T.extNorm ρ0 σ x := by
  have h1 := T.extNorm_add_le σ (c - x) x
  rw [sub_add_cancel, extNorm_sub_comm] at h1
  have h2 := T.extNorm_add_le σ (x - c) c
  rw [sub_add_cancel] at h2
  rw [max_eq_right h.le] at h1
  rcases le_total (T.extNorm ρ0 σ (x - c)) (T.extNorm ρ0 σ c) with h3 | h3
  · rw [max_eq_right h3] at h2; exact le_antisymm h1 h2
  · rw [max_eq_left h3] at h2; linarith

theorem highIndex_coeffB_mul_of {b c : T.B} {ρ ρ₁ : ℝ} (hρ0 : 0 < ρ) (hρρ₁ : ρ < ρ₁) (hρ₁ : ρ₁ < 1)
    (hb : ConvergesAt (T.coeffB b) ρ) (hb1 : ConvergesAt (T.coeffB b) ρ₁)
    (hc : ConvergesAt (T.coeffB c) ρ) (hc1 : ConvergesAt (T.coeffB c) ρ₁) (hb0 : b ≠ 0)
    (hc0 : c ≠ 0) :
    highIndex (T.coeffB (b * c)) ρ = highIndex (T.coeffB b) ρ + highIndex (T.coeffB c) ρ := by
  have hbc := (T.convergesAt_coeffB_mul hρ0 (hρρ₁.trans hρ₁) hb hc).1
  have hbc1 := (T.convergesAt_coeffB_mul (hρ0.trans hρρ₁) hρ₁ hb1 hc1).1
  have hne : ∀ {d : T.B}, d ≠ 0 → ConvergesAt (T.coeffB d) ρ → T.coeffB d ≠ 0 := by
    intro d hd hdc h0
    obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π d
    have hx0 : x ≠ 0 := by rintro rfl; exact hd (T.eq_zero_of_mul_pow (by rw [hx, map_zero]))
    rw [T.coeffB_eq hx] at h0
    apply hx0
    refine (T.zcoeff_eq_zero_iff x).1 (funext fun k => ?_)
    have := congrFun h0 (k - N)
    simpa using this
  have hbc0 : b * c ≠ 0 := by
    intro h
    have hg := (T.convergesAt_coeffB_mul hρ0 (hρρ₁.trans hρ₁) hb hc).2
    rw [h] at hg
    have h' : gaussNorm (T.coeffB (0 : T.B)) ρ = 0 := by
      rw [← map_zero (algebraMap Γ T.B), coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]
      simp [gaussNorm]
    rw [h'] at hg
    exact (mul_pos (gaussNorm_pos hρ0 hb (hne hb0 hb)) (gaussNorm_pos hρ0 hc (hne hc0 hc))).ne' hg.symm
  obtain ⟨δ1, hδ1, -, h1⟩ := exists_right_nbhd hρ0 hρρ₁ hb hb1 (hne hb0 hb)
  obtain ⟨δ2, hδ2, -, h2⟩ := exists_right_nbhd hρ0 hρρ₁ hc hc1 (hne hc0 hc)
  obtain ⟨δ3, hδ3, hδ3le, h3⟩ := exists_right_nbhd hρ0 hρρ₁ hbc hbc1 (hne hbc0 hbc)
  set ρ' := ρ + min δ1 (min δ2 δ3) / 2
  have hm : 0 < min δ1 (min δ2 δ3) := lt_min hδ1 (lt_min hδ2 hδ3)
  have hρ' : ∀ δ, min δ1 (min δ2 δ3) ≤ δ → ρ' ∈ Set.Ioo ρ (ρ + δ) := fun δ hδ =>
    ⟨by simp only [ρ']; linarith, by simp only [ρ']; linarith⟩
  have hρ'0 : 0 < ρ' := by simp only [ρ']; linarith
  have hρ'1 : ρ' < 1 := by
    have := (hρ' δ3 ((min_le_right _ _).trans (min_le_right _ _))).2; linarith
  have hρ'le : ρ' ≤ ρ₁ := by
    have := (hρ' δ3 ((min_le_right _ _).trans (min_le_right _ _))).2; linarith
  have hbρ' := hb.of_le_of_le hb1 hρ0 (hρ' δ1 (min_le_left _ _)).1.le hρ'le
  have hcρ' := hc.of_le_of_le hc1 hρ0 (hρ' δ1 (min_le_left _ _)).1.le hρ'le
  rw [← (h3 ρ' (hρ' δ3 ((min_le_right _ _).trans (min_le_right _ _)))).1,
    ← (h1 ρ' (hρ' δ1 (min_le_left _ _))).1,
    ← (h2 ρ' (hρ' δ2 ((min_le_right _ _).trans (min_le_left _ _)))).1]
  exact T.lowIndex_coeffB_mul hρ'0 hρ'1 hbρ' hcρ' hb0 hc0

theorem idx_eq_of_lt {c c' : T.Econ ρ0} {ρ ρ₁ : ℝ} (hρ0 : 0 < ρ) (hρρ₁ : ρ < ρ₁)
    (hρ₁ : ρ₁ ≤ ρ0)
    (hlt : ∀ σ : Set.Ioc (0 : ℝ) ρ0, ρ ≤ σ → (σ : ℝ) ≤ ρ₁ →
      gaussNorm (T.coeffB ((c' : T.B) - c)) σ < gaussNorm (T.coeffB c) σ) :
    lowIndex (T.coeffB c') ρ = lowIndex (T.coeffB c) ρ ∧
      highIndex (T.coeffB c') ρ = highIndex (T.coeffB c) ρ := by
  have hρ₁1 : ρ₁ < 1 := lt_of_le_of_lt hρ₁ ρ0.2.2
  set r : Set.Ioc (0 : ℝ) ρ0 := ⟨ρ, hρ0, hρρ₁.le.trans hρ₁⟩
  set r₁ : Set.Ioc (0 : ℝ) ρ0 := ⟨ρ₁, hρ0.trans hρρ₁, hρ₁⟩
  have hcr := T.convergesAt_rad ρ0 c r
  have hcr1 := T.convergesAt_rad ρ0 c r₁
  have hc'r := T.convergesAt_rad ρ0 c' r
  have hc'r1 := T.convergesAt_rad ρ0 c' r₁
  have hdr : ∀ σ : Set.Ioc (0 : ℝ) ρ0, ConvergesAt (T.coeffB ((c' : T.B) - c)) σ := fun σ =>
    T.convergesAt_rad ρ0 (c' - c) σ
  have hc0 : (c : T.B) ≠ 0 := by
    intro h0
    have := hlt r le_rfl hρρ₁.le
    rw [h0] at this
    have h' : gaussNorm (T.coeffB (0 : T.B)) ρ = 0 := by
      rw [← map_zero (algebraMap Γ T.B), coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]
      simp [gaussNorm]
    rw [h'] at this
    exact absurd this (not_lt.2 (gaussNorm_nonneg hρ0))
  have hsum : ((c : T.B) + ((c' : T.B) - c)) = c' := by ring
  have hlow := T.lowIndex_coeffB_add_of_lt hρ0 (hρρ₁.trans hρ₁1) hcr (hdr r) hc0 (hlt r le_rfl hρρ₁.le)
  rw [hsum] at hlow
  refine ⟨hlow.2, ?_⟩
  have hc'0 : (c' : T.B) ≠ 0 := by
    intro h0
    have h1 := hlow.1
    rw [h0] at h1
    have h' : gaussNorm (T.coeffB (0 : T.B)) ρ = 0 := by
      rw [← map_zero (algebraMap Γ T.B), coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]
      simp [gaussNorm]
    rw [h'] at h1
    have := hlt r le_rfl hρρ₁.le
    linarith [gaussNorm_nonneg (a := T.coeffB ((c' : T.B) - c)) hρ0]
  have hne : ∀ {d : T.B}, d ≠ 0 → T.coeffB d ≠ 0 := by
    intro d hd h0
    obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π d
    have hx0 : x ≠ 0 := by rintro rfl; exact hd (T.eq_zero_of_mul_pow (by rw [hx, map_zero]))
    rw [T.coeffB_eq hx] at h0
    apply hx0
    refine (T.zcoeff_eq_zero_iff x).1 (funext fun k => ?_)
    have := congrFun h0 (k - N)
    simpa using this
  obtain ⟨δ1, hδ1, hδ1le, h1⟩ := exists_right_nbhd hρ0 hρρ₁ hcr hcr1 (hne hc0)
  obtain ⟨δ2, hδ2, -, h2⟩ := exists_right_nbhd hρ0 hρρ₁ hc'r hc'r1 (hne hc'0)
  set ρ' := ρ + min δ1 δ2 / 2
  have hmin : 0 < min δ1 δ2 := lt_min hδ1 hδ2
  have hρ'1 : ρ' ∈ Set.Ioo ρ (ρ + δ1) :=
    ⟨by simp only [ρ']; linarith, by simp only [ρ']; linarith [min_le_left δ1 δ2]⟩
  have hρ'2 : ρ' ∈ Set.Ioo ρ (ρ + δ2) :=
    ⟨by simp only [ρ']; linarith, by simp only [ρ']; linarith [min_le_right δ1 δ2]⟩
  have hρ'le : ρ' ≤ ρ₁ := by linarith [hρ'1.2]
  set r' : Set.Ioc (0 : ℝ) ρ0 := ⟨ρ', hρ0.trans hρ'1.1, hρ'le.trans hρ₁⟩
  have hlow' := T.lowIndex_coeffB_add_of_lt (ρ := ρ') (hρ0.trans hρ'1.1)
    (lt_of_le_of_lt hρ'le hρ₁1) (T.convergesAt_rad ρ0 c r') (hdr r') hc0
    (hlt r' hρ'1.1.le hρ'le)
  rw [hsum] at hlow'
  rw [← (h1 ρ' hρ'1).1, ← (h2 ρ' hρ'2).1]
  exact hlow'.2

theorem mid_rad {ρ : ℝ} (h : 0 < ρ ∧ ρ < ρ0) :
    0 < (ρ + ρ0) / 2 ∧ (ρ + ρ0) / 2 ≤ ρ0 ∧ ρ < (ρ + ρ0) / 2 :=
  ⟨by linarith [h.1, h.2], by linarith [h.2], by linarith [h.2]⟩

def approx {x : T.RobbaExt ρ0} (hx : x ≠ 0) {ρ : ℝ} (h : 0 < ρ ∧ ρ < ρ0) : T.Econ ρ0 :=
  Classical.choose (T.exists_approx_norm hx ⟨ρ, h.1, h.2.le⟩
    ⟨(ρ + ρ0) / 2, (mid_rad h).1, (mid_rad h).2.1⟩ (mid_rad h).2.2.le)

theorem approx_spec {x : T.RobbaExt ρ0} (hx : x ≠ 0) {ρ : ℝ} (h : 0 < ρ ∧ ρ < ρ0)
    (σ : Set.Ioc (0 : ℝ) ρ0) (h1 : ρ ≤ σ) (h2 : (σ : ℝ) ≤ (ρ + ρ0) / 2) :
    T.extNorm ρ0 σ (x - T.approx hx h) < T.extNorm ρ0 σ x :=
  Classical.choose_spec (T.exists_approx_norm hx ⟨ρ, h.1, h.2.le⟩
    ⟨(ρ + ρ0) / 2, (mid_rad h).1, (mid_rad h).2.1⟩ (mid_rad h).2.2.le) σ h1 h2

open Classical in

def lowIdx (x : T.RobbaExt ρ0) (ρ : ℝ) : ℤ :=
  if h : x ≠ 0 ∧ 0 < ρ ∧ ρ < ρ0 then lowIndex (T.coeffB (T.approx h.1 h.2)) ρ else 0

open Classical in

def highIdx (x : T.RobbaExt ρ0) (ρ : ℝ) : ℤ :=
  if h : x ≠ 0 ∧ 0 < ρ ∧ ρ < ρ0 then highIndex (T.coeffB (T.approx h.1 h.2)) ρ else 0

def mult (x : T.RobbaExt ρ0) (ρ : ℝ) : ℤ := T.highIdx x ρ - T.lowIdx x ρ

theorem idx_eq_of_approx {x : T.RobbaExt ρ0} (hx : x ≠ 0) {ρ : ℝ} (h : 0 < ρ ∧ ρ < ρ0)
    {c : T.Econ ρ0} {η : ℝ} (hη : 0 < η) (hηle : ρ + η ≤ ρ0)
    (hc : ∀ σ : Set.Ioc (0 : ℝ) ρ0, ρ ≤ σ → (σ : ℝ) ≤ ρ + η →
      T.extNorm ρ0 σ (x - c) < T.extNorm ρ0 σ x) :
    T.lowIdx x ρ = lowIndex (T.coeffB c) ρ ∧ T.highIdx x ρ = highIndex (T.coeffB c) ρ := by
  have hh : x ≠ 0 ∧ 0 < ρ ∧ ρ < ρ0 := ⟨hx, h⟩
  rw [lowIdx, highIdx, dif_pos hh, dif_pos hh]
  set c₀ := T.approx hx h
  set ρ₁ := min (ρ + η) ((ρ + ρ0) / 2)
  have hρρ₁ : ρ < ρ₁ := lt_min (by linarith) (mid_rad h).2.2
  have hρ₁ : ρ₁ ≤ ρ0 := (min_le_right _ _).trans (mid_rad h).2.1
  have key : ∀ σ : Set.Ioc (0 : ℝ) ρ0, ρ ≤ σ → (σ : ℝ) ≤ ρ₁ →
      gaussNorm (T.coeffB ((c : T.B) - c₀)) σ < gaussNorm (T.coeffB c₀) σ := fun σ h1 h2 => by
    have e1 := T.approx_spec hx h σ h1 (h2.trans (min_le_right _ _))
    have e2 := hc σ h1 (h2.trans (min_le_left _ _))
    have e3 : T.extNorm ρ0 σ ((c₀ : T.RobbaExt ρ0) - c) < T.extNorm ρ0 σ x := by
      have := T.extNorm_add_le σ ((c : T.RobbaExt ρ0) - x) (x - c₀)
      rw [show (c : T.RobbaExt ρ0) - x + (x - c₀) = c - c₀ by ring, extNorm_sub_comm,
        extNorm_sub_comm] at this
      rw [extNorm_sub_comm]
      exact this.trans_lt (max_lt (by rw [extNorm_sub_comm]; exact e2) e1)
    rw [← T.extNorm_eq_of_lt e1, T.extNorm_coe, extNorm_sub_comm, ← Completion.coe_sub,
      T.extNorm_coe] at e3
    exact e3
  obtain ⟨hl, hh'⟩ := T.idx_eq_of_lt (c := c₀) (c' := c) h.1 hρρ₁ hρ₁ key
  exact ⟨hl.symm, hh'.symm⟩

theorem extNorm_mul_sub_lt {x y : T.RobbaExt ρ0} {c e : T.RobbaExt ρ0} {σ : Set.Ioc (0 : ℝ) ρ0}
    (hc : T.extNorm ρ0 σ (x - c) < T.extNorm ρ0 σ x)
    (he : T.extNorm ρ0 σ (y - e) < T.extNorm ρ0 σ y) :
    T.extNorm ρ0 σ (x * y - c * e) < T.extNorm ρ0 σ (x * y) := by
  have hx : 0 < T.extNorm ρ0 σ x := lt_of_le_of_lt (T.extNorm_nonneg σ _) hc
  have hy : 0 < T.extNorm ρ0 σ y := lt_of_le_of_lt (T.extNorm_nonneg σ _) he
  have hE : T.extNorm ρ0 σ e = T.extNorm ρ0 σ y := T.extNorm_eq_of_lt he
  have := T.extNorm_add_le σ (x * (y - e)) ((x - c) * e)
  rw [show x * (y - e) + (x - c) * e = x * y - c * e by ring, extNorm_mul, extNorm_mul, hE] at this
  rw [extNorm_mul]
  refine this.trans_lt (max_lt ?_ ?_)
  · exact mul_lt_mul_of_pos_left he hx
  · exact mul_lt_mul_of_pos_right hc hy

theorem coe_ne_zero_of_approx {x : T.RobbaExt ρ0} {c : T.Econ ρ0} {σ : Set.Ioc (0 : ℝ) ρ0}
    (hc : T.extNorm ρ0 σ (x - c) < T.extNorm ρ0 σ x) : (c : T.B) ≠ 0 := by
  intro h0
  have : (c : T.RobbaExt ρ0) = 0 := by
    rw [show c = 0 from Subtype.ext h0, Completion.coe_zero]
  rw [this, sub_zero] at hc
  exact lt_irrefl _ hc

theorem lowIdx_eq_approx {x : T.RobbaExt ρ0} (hx : x ≠ 0) {ρ : ℝ} (h : 0 < ρ ∧ ρ < ρ0) :
    T.lowIdx x ρ = lowIndex (T.coeffB (T.approx hx h)) ρ := by
  rw [lowIdx, dif_pos ⟨hx, h⟩]

theorem highIdx_eq_approx {x : T.RobbaExt ρ0} (hx : x ≠ 0) {ρ : ℝ} (h : 0 < ρ ∧ ρ < ρ0) :
    T.highIdx x ρ = highIndex (T.coeffB (T.approx hx h)) ρ := by
  rw [highIdx, dif_pos ⟨hx, h⟩]

theorem idx_mul {x y : T.RobbaExt ρ0} (hx : x ≠ 0) (hy : y ≠ 0) {ρ : ℝ} (h : 0 < ρ ∧ ρ < ρ0) :
    T.lowIdx (x * y) ρ = T.lowIdx x ρ + T.lowIdx y ρ ∧
      T.highIdx (x * y) ρ = T.highIdx x ρ + T.highIdx y ρ := by
  set c := T.approx hx h
  set e := T.approx hy h
  have hη : 0 < (ρ0 - ρ) / 2 := by linarith [h.2]
  have hηle : ρ + (ρ0 - ρ) / 2 ≤ ρ0 := by linarith [h.2]
  have hmid : ρ + (ρ0 - ρ) / 2 = (ρ + ρ0) / 2 := by ring
  have hce : ∀ σ : Set.Ioc (0 : ℝ) ρ0, ρ ≤ σ → (σ : ℝ) ≤ ρ + (ρ0 - ρ) / 2 →
      T.extNorm ρ0 σ (x * y - ((c * e : T.Econ ρ0) : T.RobbaExt ρ0)) < T.extNorm ρ0 σ (x * y) := by
    intro σ h1 h2
    rw [hmid] at h2
    rw [Completion.coe_mul]
    exact T.extNorm_mul_sub_lt (T.approx_spec hx h σ h1 h2) (T.approx_spec hy h σ h1 h2)
  obtain ⟨hl, hh⟩ := T.idx_eq_of_approx (mul_ne_zero hx hy) h hη hηle hce
  set r : Set.Ioc (0 : ℝ) ρ0 := ⟨ρ, h.1, h.2.le⟩
  have hc0 : (c : T.B) ≠ 0 := T.coe_ne_zero_of_approx (T.approx_spec hx h r le_rfl (mid_rad h).2.2.le)
  have he0 : (e : T.B) ≠ 0 := T.coe_ne_zero_of_approx (T.approx_spec hy h r le_rfl (mid_rad h).2.2.le)
  set r₁ : Set.Ioc (0 : ℝ) ρ0 := ⟨(ρ + ρ0) / 2, (mid_rad h).1, (mid_rad h).2.1⟩
  rw [hl, hh, T.lowIdx_eq_approx hx h, T.lowIdx_eq_approx hy h, T.highIdx_eq_approx hx h,
    T.highIdx_eq_approx hy h]
  refine ⟨T.lowIndex_coeffB_mul h.1 (h.2.trans ρ0.2.2) (T.convergesAt_rad ρ0 c r)
      (T.convergesAt_rad ρ0 e r) hc0 he0, ?_⟩
  exact T.highIndex_coeffB_mul_of h.1 (mid_rad h).2.2 (lt_of_le_of_lt (mid_rad h).2.1 ρ0.2.2)
    (T.convergesAt_rad ρ0 c r) (T.convergesAt_rad ρ0 c r₁) (T.convergesAt_rad ρ0 e r)
    (T.convergesAt_rad ρ0 e r₁) hc0 he0

theorem lowIdx_le_highIdx (x : T.RobbaExt ρ0) (ρ : ℝ) : T.lowIdx x ρ ≤ T.highIdx x ρ := by
  by_cases hh : x ≠ 0 ∧ 0 < ρ ∧ ρ < ρ0
  · rw [T.lowIdx_eq_approx hh.1 hh.2, T.highIdx_eq_approx hh.1 hh.2]
    set r : Set.Ioc (0 : ℝ) ρ0 := ⟨ρ, hh.2.1, hh.2.2.le⟩
    have hc0 := T.coe_ne_zero_of_approx (T.approx_spec hh.1 hh.2 r le_rfl (mid_rad hh.2).2.2.le)
    refine lowIndex_le_highIndex hh.2.1 (T.convergesAt_rad ρ0 _ r) fun h0 => ?_
    obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj T.π ((T.approx hh.1 hh.2 : T.Econ ρ0) : T.B)
    have hy0 : y ≠ 0 := by rintro rfl; exact hc0 (T.eq_zero_of_mul_pow (by rw [hy, map_zero]))
    rw [T.coeffB_eq hy] at h0
    apply hy0
    refine (T.zcoeff_eq_zero_iff y).1 (funext fun k => ?_)
    have := congrFun h0 (k - N)
    simpa using this
  · rw [lowIdx, highIdx, dif_neg hh, dif_neg hh]

theorem mult_nonneg (x : T.RobbaExt ρ0) (ρ : ℝ) : 0 ≤ T.mult x ρ :=
  sub_nonneg.2 (T.lowIdx_le_highIdx x ρ)

theorem mult_mul {x y : T.RobbaExt ρ0} (hx : x ≠ 0) (hy : y ≠ 0) {ρ : ℝ} (h : 0 < ρ ∧ ρ < ρ0) :
    T.mult (x * y) ρ = T.mult x ρ + T.mult y ρ := by
  obtain ⟨h1, h2⟩ := T.idx_mul hx hy h
  simp only [mult, h1, h2]; ring

theorem idx_coe {b : T.Econ ρ0} (hb : (b : T.RobbaExt ρ0) ≠ 0) {ρ : ℝ} (h : 0 < ρ ∧ ρ < ρ0) :
    T.lowIdx (b : T.RobbaExt ρ0) ρ = lowIndex (T.coeffB b) ρ ∧
      T.highIdx (b : T.RobbaExt ρ0) ρ = highIndex (T.coeffB b) ρ := by
  have hη : 0 < (ρ0 - ρ) / 2 := by linarith [h.2]
  refine T.idx_eq_of_approx hb h hη (by linarith [h.2]) fun σ _ _ => ?_
  rw [sub_self, extNorm_zero]
  exact T.extNorm_pos hb σ

theorem idx_single_zero_one {ρ : ℝ} (hρ : 0 < ρ) :
    lowIndex (Pi.single 0 (1 : L)) ρ = 0 ∧ highIndex (Pi.single 0 (1 : L)) ρ = 0 := by
  have hc := convergesAt_pi_single (L := L) 0 1 ρ
  have hne : (Pi.single 0 (1 : L) : ℤ → L) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  have key : ∀ n : ℤ, (Pi.single 0 (1 : L) : ℤ → L) n ≠ 0 → n = 0 := fun n hn => by
    by_contra h
    apply hn
    rw [Pi.single_apply, if_neg h]
  exact ⟨key _ (ne_zero_of_mem_domSet hρ hc hne (lowIndex_mem hρ hc hne)),
    key _ (ne_zero_of_mem_domSet hρ hc hne (highIndex_mem hρ hc hne))⟩

theorem mult_one {ρ : ℝ} (h : 0 < ρ ∧ ρ < ρ0) : T.mult (1 : T.RobbaExt ρ0) ρ = 0 := by
  have h1 : ((1 : T.Econ ρ0) : T.RobbaExt ρ0) ≠ 0 := by
    rw [Completion.coe_one]; exact one_ne_zero
  obtain ⟨hl, hh⟩ := T.idx_coe h1 h
  rw [Completion.coe_one] at hl hh
  have hc : T.coeffB ((1 : T.Econ ρ0) : T.B) = Pi.single 0 1 := by
    show T.coeffB 1 = _
    rw [← map_one (algebraMap Γ T.B), coeffB_algebraMap, zcoeff_one]
  rw [mult, hl, hh, hc, (idx_single_zero_one h.1).1, (idx_single_zero_one h.1).2, sub_self]

def breaksR (x : T.RobbaExt ρ0) (a b : ℝ) : Set ℝ :=
  {ρ | ρ ∈ Set.Icc a b ∧ T.lowIdx x ρ < T.highIdx x ρ}

theorem exists_approx_interval {x : T.RobbaExt ρ0} (hx : x ≠ 0) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < ρ0) :
    ∃ c : T.Econ ρ0, T.coeffB c ≠ 0 ∧ ∀ ρ ∈ Set.Icc a b,
      T.lowIdx x ρ = lowIndex (T.coeffB c) ρ ∧ T.highIdx x ρ = highIndex (T.coeffB c) ρ := by
  have hb' : (b + ρ0) / 2 ≤ ρ0 := by linarith
  obtain ⟨c, hc⟩ := T.exists_approx_norm hx ⟨a, ha, hab.trans hb.le⟩
    ⟨(b + ρ0) / 2, by linarith, hb'⟩ (by show a ≤ (b + ρ0) / 2; linarith)
  refine ⟨c, ?_, fun ρ hρ => ?_⟩
  · intro h0
    have hc1 := hc ⟨a, ha, hab.trans hb.le⟩ le_rfl (by show a ≤ (b + ρ0) / 2; linarith)
    have hc0 := T.coe_ne_zero_of_approx hc1
    obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj T.π (c : T.B)
    have hy0 : y ≠ 0 := by rintro rfl; exact hc0 (T.eq_zero_of_mul_pow (by rw [hy, map_zero]))
    rw [T.coeffB_eq hy] at h0
    apply hy0
    refine (T.zcoeff_eq_zero_iff y).1 (funext fun k => ?_)
    have := congrFun h0 (k - N)
    simpa using this
  · have hρ0 : 0 < ρ := ha.trans_le hρ.1
    refine T.idx_eq_of_approx hx ⟨hρ0, hρ.2.trans_lt hb⟩ (η := (b + ρ0) / 2 - ρ) (by linarith [hρ.2])
      (by linarith) fun σ h1 h2 => hc σ (hρ.1.trans h1) (by linarith)

theorem breaksR_finite {x : T.RobbaExt ρ0} (hx : x ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < ρ0) : (T.breaksR x a b).Finite := by
  obtain ⟨c, hc0, hc⟩ := T.exists_approx_interval hx ha hab hb
  have heq : T.breaksR x a b = breaks (T.coeffB c) a b := by
    ext ρ
    simp only [breaksR, breaks, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hρ, hlt⟩; rw [(hc ρ hρ).1, (hc ρ hρ).2] at hlt; exact ⟨hρ, hlt⟩
    · rintro ⟨hρ, hlt⟩; rw [← (hc ρ hρ).1, ← (hc ρ hρ).2] at hlt; exact ⟨hρ, hlt⟩
  rw [heq]
  exact breaks_finite ha hab (T.convergesAt_rad ρ0 c ⟨a, ha, hab.trans hb.le⟩)
    (T.convergesAt_rad ρ0 c ⟨b, ha.trans_le hab, hb.le⟩) hc0

theorem sum_mult_breaksR {x : T.RobbaExt ρ0} (hx : x ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < ρ0) :
    ∑ ρ ∈ (T.breaksR_finite hx ha hab hb).toFinset, T.mult x ρ = T.highIdx x b - T.lowIdx x a := by
  obtain ⟨c, hc0, hc⟩ := T.exists_approx_interval hx ha hab hb
  have hA := T.convergesAt_rad ρ0 c ⟨a, ha, hab.trans hb.le⟩
  have hB := T.convergesAt_rad ρ0 c ⟨b, ha.trans_le hab, hb.le⟩
  have hset : (T.breaksR_finite hx ha hab hb).toFinset = (breaks_finite ha hab hA hB hc0).toFinset := by
    ext ρ
    simp only [Set.Finite.mem_toFinset, breaksR, breaks, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hρ, hlt⟩; rw [(hc ρ hρ).1, (hc ρ hρ).2] at hlt; exact ⟨hρ, hlt⟩
    · rintro ⟨hρ, hlt⟩; rw [← (hc ρ hρ).1, ← (hc ρ hρ).2] at hlt; exact ⟨hρ, hlt⟩
  rw [hset, (hc b ⟨hab, le_rfl⟩).2, (hc a ⟨le_rfl, hab⟩).1, ← sum_slopeMult_breaks ha hab hA hB hc0]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have hρ' : ρ ∈ Set.Icc a b := by
    simp only [Set.Finite.mem_toFinset, breaks, Set.mem_setOf_eq] at hρ; exact hρ.1
  rw [mult, (hc ρ hρ').1, (hc ρ hρ').2, slopeMult]

end TeichLift

end GroundTheory.PAdicHodge
