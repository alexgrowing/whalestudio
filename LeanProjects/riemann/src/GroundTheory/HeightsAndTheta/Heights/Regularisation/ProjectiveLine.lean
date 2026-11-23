import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open GroundTheory.Heights₂.Heights (CP)
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace ProjectiveLine

theorem norm_fin_one_eq (y : Fin 1 → ℂ) : ‖y‖ = ‖y 0‖ := by
  have h : y = fun _ => y 0 := funext fun i => by rw [Subsingleton.elim i 0]
  conv_lhs => rw [h]
  exact pi_norm_const _

theorem limsup_zero_real {α : Type*} (F : Filter α) : limsup (fun _ : α => (0 : ℝ)) F = 0 := by
  rcases F.eq_or_neBot with rfl | hF
  · simp only [Filter.limsup, Filter.limsSup, Filter.map_bot, Filter.eventually_bot, Set.ofPred_true]
    exact Real.sInf_of_not_bddBelow not_bddBelow_univ
  · exact limsup_const 0

theorem analyticAt_chartVec_apply {N : ℕ} (i m : Fin (N + 1)) (z : Fin N → ℂ) :
    AnalyticAt ℂ (fun z : Fin N → ℂ => CP.chartVec i z m) z := by
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m
  · simp only [CP.chartVec_self]; exact analyticAt_const
  · simp only [CP.chartVec_succAbove]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).analyticAt z

theorem analyticOnNhd_transition {N : ℕ} (i j : Fin (N + 1)) :
    AnalyticOnNhd ℂ (fun z => CP.chartCoord j (CP.chartInv i z)) {z | CP.chartVec i z j ≠ 0} := by
  intro z hz
  simp only [CP.chartCoord_chartInv_eq]
  rw [analyticAt_pi_iff]
  intro k
  exact (analyticAt_chartVec_apply i _ z).div (analyticAt_chartVec_apply i j z) hz

def cpAtlas : FinHolAtlas 1 (CP 1) where
  n := 2
  chart := CP.chart
  cover x := CP.exists_mem_chartDomain x
  holo j k := fun z hz => analyticOnNhd_transition j k z hz.2

def sChart (i : Fin 2) : OpenPartialHomeomorph (CP 1) (Fin 1 → ℂ) where
  toFun x := (2 : ℂ)⁻¹ • CP.chartCoord i x
  invFun y := CP.chartInv i ((2 : ℂ) • y)
  source := CP.chartDomain i ∩ CP.chartCoord i ⁻¹' ball 0 2
  target := ball 0 1
  map_source' x hx := by
    have h := hx.2
    simp only [mem_preimage, mem_ball_zero_iff] at h ⊢
    rw [norm_smul]
    norm_num
    linarith
  map_target' y hy := by
    refine ⟨CP.chartInv_mem i _, ?_⟩
    simp only [mem_preimage, CP.chartCoord_chartInv, mem_ball_zero_iff] at hy ⊢
    rw [norm_smul]
    norm_num
    linarith
  left_inv' x hx := by
    simp only [smul_smul]
    norm_num
    exact CP.chartInv_chartCoord i hx.1
  right_inv' y _ := by
    simp only [CP.chartCoord_chartInv, smul_smul]
    norm_num
  open_source := (CP.continuousOn_chartCoord i).isOpen_inter_preimage (CP.isOpen_chartDomain i)
    isOpen_ball
  open_target := isOpen_ball
  continuousOn_toFun := ((CP.continuousOn_chartCoord i).mono inter_subset_left).const_smul ((2 : ℂ)⁻¹)
  continuousOn_invFun := ((CP.continuous_chartInv i).comp (continuous_const_smul _)).continuousOn

theorem sChart_apply (i : Fin 2) (x : CP 1) : sChart i x = (2 : ℂ)⁻¹ • CP.chartCoord i x := rfl

theorem sChart_symm_apply (i : Fin 2) (y : Fin 1 → ℂ) :
    (sChart i).symm y = CP.chartInv i ((2 : ℂ) • y) := rfl

theorem sChart_source (i : Fin 2) :
    (sChart i).source = CP.chartDomain i ∩ CP.chartCoord i ⁻¹' ball 0 2 := rfl

theorem sChart_target (i : Fin 2) : (sChart i).target = ball 0 1 := rfl

theorem sChart_compat (i : Fin 2) : IsCompatChart cpAtlas (sChart i) := by
  intro j
  refine ⟨fun z hz => ?_, fun y hy => ?_⟩
  · have h1 : CP.chartVec j z i ≠ 0 := hz.2.1
    have := (analyticOnNhd_transition j i z h1).const_smul (c := (2 : ℂ)⁻¹)
    exact this
  · have h1 : CP.chartVec i ((2 : ℂ) • y) j ≠ 0 := hy.2
    have hlin : AnalyticAt ℂ (fun y : Fin 1 → ℂ => (2 : ℂ) • y) y :=
      ((2 : ℂ) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ)).analyticAt y
    exact (analyticOnNhd_transition i j _ h1).comp hlin

def closedReg (i : Fin 2) (c : ℝ) : Set (CP 1) :=
  {x | x ∈ CP.chartDomain i ∧ ‖CP.chartCoord i x‖ ≤ c}

theorem fin_two_other (i : Fin 2) (m : Fin 2) : m = i ∨ m = i.succAbove 0 := by
  fin_cases i <;> fin_cases m <;> simp

theorem isClosed_closedReg (i : Fin 2) {c : ℝ} (hc : 0 ≤ c) : IsClosed (closedReg i c) := by
  rw [GroundTheory.Heights₂.Heights.ProjTopology.isClosed_iff]
  have : (Projectivization.mk' ℂ) ⁻¹' (closedReg i c) =
      {v : {v : Fin 2 → ℂ // v ≠ 0} | ‖v.1 (i.succAbove 0)‖ ≤ c * ‖v.1 i‖} := by
    ext ⟨v, hv⟩
    simp only [closedReg, mem_preimage, Set.mem_ofPred_eq]
    change (v i ≠ 0 ∧ ‖fun j => v (i.succAbove j) / v i‖ ≤ c) ↔ _
    rw [norm_fin_one_eq]
    constructor
    · rintro ⟨hvi, h⟩
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hvi)] at h
      exact h
    · intro h
      have hvi : v i ≠ 0 := by
        intro h0
        rw [h0, norm_zero, mul_zero] at h
        have h1 : v (i.succAbove 0) = 0 := norm_le_zero_iff.mp h
        apply hv
        funext m
        rcases fin_two_other i m with rfl | rfl
        · exact h0
        · exact h1
      refine ⟨hvi, ?_⟩
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hvi)]
      exact h
  rw [this]
  have hf : Continuous fun v : {v : Fin 2 → ℂ // v ≠ 0} => ‖v.1 (i.succAbove 0)‖ :=
    ((continuous_apply (i.succAbove 0)).comp continuous_subtype_val).norm
  have hg : Continuous fun v : {v : Fin 2 → ℂ // v ≠ 0} => c * ‖v.1 i‖ :=
    continuous_const.mul ((continuous_apply i).comp continuous_subtype_val).norm
  exact isClosed_le hf hg

theorem mem_sChart_source_iff (i : Fin 2) (x : CP 1) :
    x ∈ (sChart i).source ↔ x ∈ CP.chartDomain i ∧ ‖CP.chartCoord i x‖ < 2 := by
  simp [sChart_source]

theorem norm_sChart (i : Fin 2) (x : CP 1) : ‖sChart i x‖ = ‖CP.chartCoord i x‖ / 2 := by
  rw [sChart_apply, norm_smul]
  norm_num
  ring

def cpMid (i : Fin 2) : Set (CP 1) := (sChart i).source ∩ sChart i ⁻¹' ball 0 (7 / 8)

def cpInner (i : Fin 2) : Set (CP 1) := (sChart i).source ∩ sChart i ⁻¹' ball 0 (3 / 4)

theorem mem_region_iff (i : Fin 2) (x : CP 1) {c : ℝ} (_hc : c ≤ 1) :
    x ∈ (sChart i).source ∩ sChart i ⁻¹' ball 0 c ↔
      x ∈ CP.chartDomain i ∧ ‖CP.chartCoord i x‖ < 2 * c := by
  rw [mem_inter_iff, mem_sChart_source_iff, mem_preimage, mem_ball_zero_iff, norm_sChart]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, by linarith⟩

theorem region_subset_closedReg (i : Fin 2) {c : ℝ} (hc : c ≤ 1) :
    (sChart i).source ∩ sChart i ⁻¹' ball 0 c ⊆ closedReg i (2 * c) := fun x hx => by
  obtain ⟨h1, h2⟩ := (mem_region_iff i x hc).1 hx
  exact ⟨h1, h2.le⟩

theorem closedReg_subset_region (i : Fin 2) {c d : ℝ} (hd : d ≤ 1) (hcd : c < 2 * d) :
    closedReg i c ⊆ (sChart i).source ∩ sChart i ⁻¹' ball 0 d := fun x hx =>
  (mem_region_iff i x hd).2 ⟨hx.1, lt_of_le_of_lt hx.2 hcd⟩

theorem closure_region_subset (i : Fin 2) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1) :
    closure ((sChart i).source ∩ sChart i ⁻¹' ball 0 c) ⊆ closedReg i (2 * c) :=
  closure_minimal (region_subset_closedReg i hc) (isClosed_closedReg i (by linarith))

theorem cover_inner (x : CP 1) : ∃ j, x ∈ cpInner j := by
  induction x using Projectivization.ind with
  | h v hv =>
    rcases le_or_gt ‖v 1‖ ‖v 0‖ with h | h
    · have h0 : v 0 ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at h
        apply hv; funext m; fin_cases m
        · exact h0
        · exact norm_le_zero_iff.mp h
      refine ⟨0, (mem_region_iff 0 _ (by norm_num)).2 ⟨h0, ?_⟩⟩
      rw [CP.chartCoord_mk, norm_fin_one_eq]
      simp only [norm_div]
      rw [div_lt_iff₀ (norm_pos_iff.mpr h0)]
      have : (Fin.succAbove (0 : Fin 2) 0) = 1 := rfl
      rw [this]
      have := norm_pos_iff.mpr h0
      nlinarith
    · have h1 : v 1 ≠ 0 := fun h1 => by rw [h1, norm_zero] at h; exact absurd h (not_lt.2 (norm_nonneg _))
      refine ⟨1, (mem_region_iff 1 _ (by norm_num)).2 ⟨h1, ?_⟩⟩
      rw [CP.chartCoord_mk, norm_fin_one_eq]
      simp only [norm_div]
      rw [div_lt_iff₀ (norm_pos_iff.mpr h1)]
      have : (Fin.succAbove (1 : Fin 2) 0) = 0 := rfl
      rw [this]
      nlinarith [norm_nonneg (v 0)]

theorem holoOn_zero' {D : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas D X) (W : Set X) :
    A.HoloOn W (fun _ => (0 : ℂ)) :=
  fun _ => analyticOnNhd_const

def cpCharts : PotentialCharts cpAtlas where
  N := 2
  chart := sChart
  compat := sChart_compat
  target_subset _ := subset_rfl
  mid := cpMid
  inner := cpInner
  isOpen_mid i := (sChart i).isOpen_inter_preimage isOpen_ball
  isOpen_inner i := (sChart i).isOpen_inter_preimage isOpen_ball
  closure_inner i := by
    refine (closure_region_subset i (by norm_num) (by norm_num)).trans ?_
    exact closedReg_subset_region i (by norm_num) (by norm_num)
  closure_mid i := by
    refine (closure_region_subset i (by norm_num) (by norm_num)).trans ?_
    exact (closedReg_subset_region i (d := 1) le_rfl (by norm_num)).trans inter_subset_left
  cover := cover_inner
  th := LocPot.ofFun (fun _ => 0)
  th_pot := ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ fun _ => contDiffOn_const
  q _ _ := 0
  q_smooth _ := contDiffOn_const
  q_th _ _ y _ := ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, holoOn_zero' _ _,
    fun _ _ => by simp [LocPot.ofFun]⟩

def ltSet (a b : Fin 2) : Set (CP 1) :=
  {x | Projectivization.lift (fun v : {v : Fin 2 → ℂ // v ≠ 0} => ‖v.1 a‖ < ‖v.1 b‖) (by
    rintro ⟨u, hu⟩ ⟨w, hw⟩ t rfl
    have ht : t ≠ 0 := by rintro rfl; simp at hu
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact propext (mul_lt_mul_iff_right₀ (norm_pos_iff.mpr ht))) x}

theorem mk_mem_ltSet (a b : Fin 2) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ ltSet a b ↔ ‖v a‖ < ‖v b‖ := Iff.rfl

theorem isOpen_ltSet (a b : Fin 2) : IsOpen (ltSet a b) := by
  rw [GroundTheory.Heights₂.Heights.ProjTopology.isOpen_iff]
  have : (Projectivization.mk' ℂ) ⁻¹' (ltSet a b) =
      {v : {v : Fin 2 → ℂ // v ≠ 0} | ‖v.1 a‖ < ‖v.1 b‖} := by
    ext ⟨v, hv⟩; exact Iff.rfl
  rw [this]
  exact isOpen_lt ((continuous_apply a).comp continuous_subtype_val).norm
    ((continuous_apply b).comp continuous_subtype_val).norm

theorem mem_ltSet_of_not_mem (a b : Fin 2) (hab : a ≠ b) (x : CP 1) (hx : x ∉ CP.chartDomain a) :
    x ∈ ltSet a b := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [CP.mk_mem_chartDomain, not_not] at hx
    rw [mk_mem_ltSet, hx, norm_zero, norm_pos_iff]
    intro hb
    apply hv
    funext m
    fin_cases a <;> fin_cases b <;> fin_cases m <;> simp_all

instance t2Space_complexProjLine : T2Space (CP 1) := by
  refine ⟨fun x y hxy => ?_⟩
  have key : ∀ i : Fin 2, x ∈ CP.chartDomain i → y ∈ CP.chartDomain i →
      ∃ u v : Set (CP 1), IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v := by
    intro i hx hy
    have hne : CP.chartCoord i x ≠ CP.chartCoord i y := fun h => hxy (by
      rw [← CP.chartInv_chartCoord i hx, h, CP.chartInv_chartCoord i hy])
    obtain ⟨u', v', hu', hv', hxu, hyv, huv⟩ := t2_separation hne
    refine ⟨CP.chartDomain i ∩ CP.chartCoord i ⁻¹' u', CP.chartDomain i ∩ CP.chartCoord i ⁻¹' v',
      (CP.continuousOn_chartCoord i).isOpen_inter_preimage (CP.isOpen_chartDomain i) hu',
      (CP.continuousOn_chartCoord i).isOpen_inter_preimage (CP.isOpen_chartDomain i) hv',
      ⟨hx, hxu⟩, ⟨hy, hyv⟩, ?_⟩
    exact Set.disjoint_left.2 fun z hz hz' => Set.disjoint_left.1 huv hz.2 hz'.2
  have hdisj : Disjoint (ltSet 0 1) (ltSet 1 0) :=
    Set.disjoint_left.2 fun z hz hz' => by
      induction z using Projectivization.ind with
      | h v hv =>
        rw [mk_mem_ltSet] at hz hz'
        exact lt_asymm hz hz'
  by_cases h0 : x ∈ CP.chartDomain 0 ∧ y ∈ CP.chartDomain 0
  · exact key 0 h0.1 h0.2
  by_cases h1 : x ∈ CP.chartDomain 1 ∧ y ∈ CP.chartDomain 1
  · exact key 1 h1.1 h1.2
  by_cases hx0 : x ∈ CP.chartDomain 0
  ·
    have hy0 : y ∉ CP.chartDomain 0 := fun hy => h0 ⟨hx0, hy⟩
    have hx1 : x ∉ CP.chartDomain 1 := by
      intro hx1
      obtain ⟨i, hi⟩ := CP.exists_mem_chartDomain y
      fin_cases i
      · exact hy0 hi
      · exact h1 ⟨hx1, hi⟩
    exact ⟨ltSet 1 0, ltSet 0 1, isOpen_ltSet 1 0, isOpen_ltSet 0 1,
      mem_ltSet_of_not_mem 1 0 (by decide) x hx1, mem_ltSet_of_not_mem 0 1 (by decide) y hy0,
      hdisj.symm⟩
  · have hy1 : y ∉ CP.chartDomain 1 := by
      intro hy1
      obtain ⟨i, hi⟩ := CP.exists_mem_chartDomain x
      fin_cases i
      · exact hx0 hi
      · exact h1 ⟨hi, hy1⟩
    exact ⟨ltSet 0 1, ltSet 1 0, isOpen_ltSet 0 1, isOpen_ltSet 1 0,
      mem_ltSet_of_not_mem 0 1 (by decide) x hx0, mem_ltSet_of_not_mem 1 0 (by decide) y hy1,
      hdisj⟩

def cpS (j : Fin 2) : Finset (Fin 1) := if (j : ℕ) = 0 then {0} else ∅

def cpF (j : Fin 2) (y : Fin 1 → ℂ) : ℝ :=
  if (j : ℕ) = 0 then Real.log (1 + ‖(2 : ℂ) * y 0‖ ^ 2) - Real.log 4
  else Real.log (1 + ‖(2 : ℂ) * y 0‖ ^ 2)

def cpR (x : CP 1) : ℝ := Real.exp 1 + Real.log (1 + ‖CP.chartCoord 1 x 0‖ ^ 2)

theorem chartVec_zero_one (z : Fin 1 → ℂ) : CP.chartVec 0 z 1 = z 0 :=
  CP.chartVec_succAbove 0 z 0

theorem chartVec_one_zero (z : Fin 1 → ℂ) : CP.chartVec 1 z 0 = z 0 :=
  CP.chartVec_succAbove 1 z 0

theorem cp_mem_Yo (j : Fin 2) (x : CP 1) (hx : x ∈ (sChart j).source) :
    x ∈ CP.chartDomain 1 ↔ sChart j x ∉ coordDiv (cpS j) := by
  fin_cases j
  · have hx0 : x ∈ CP.chartDomain 0 := hx.1
    simp only [cpS, coordDiv, Fin.zero_eta, Fin.isValue, Fin.val_zero, if_true,
      Finset.mem_singleton, exists_eq_left, Set.mem_ofPred_eq, sChart_apply, Pi.smul_apply, smul_eq_mul,
      mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
    induction x using Projectivization.ind with
    | h v hv =>
      rw [CP.mk_mem_chartDomain] at hx0 ⊢
      rw [CP.chartCoord_mk]
      have : (Fin.succAbove (0 : Fin 2) 0) = 1 := rfl
      simp only [this, div_eq_zero_iff, hx0, or_false]
  · simp only [cpS, coordDiv, Fin.mk_one, Fin.isValue, Fin.val_one, one_ne_zero, if_false,
      Finset.notMem_empty, false_and, exists_false, Set.ofPred_false, mem_empty_iff_false,
      not_false_eq_true, iff_true]
    exact hx.1

theorem contDiff_logNormSq : ContDiff ℝ ∞ (fun y : Fin 1 → ℂ => Real.log (1 + ‖(2 : ℂ) * y 0‖ ^ 2)) := by
  have h2 : ContDiff ℝ ∞ (fun y : Fin 1 → ℂ => (2 : ℂ) * y 0) :=
    contDiff_const.mul (contDiff_apply ℝ ℂ 0)
  exact (contDiff_const.add ((contDiff_norm_sq ℝ).comp h2)).log fun y =>
    (by positivity : (0 : ℝ) < 1 + ‖(2 : ℂ) * y 0‖ ^ 2).ne'

theorem cpF_bound (j : Fin 2) (y : Fin 1 → ℂ) (hy : y ∈ ball (0 : Fin 1 → ℂ) 1) : |cpF j y| ≤ 8 := by
  have hy0 : ‖y 0‖ < 1 := by
    rw [mem_ball_zero_iff, norm_fin_one_eq] at hy; exact hy
  have hs : ‖(2 : ℂ) * y 0‖ ^ 2 < 4 := by
    rw [norm_mul]; norm_num
    nlinarith [norm_nonneg (y 0)]
  have h1 : 0 ≤ Real.log (1 + ‖(2 : ℂ) * y 0‖ ^ 2) := Real.log_nonneg (by nlinarith [norm_nonneg ((2 : ℂ) * y 0)])
  have h2 : Real.log (1 + ‖(2 : ℂ) * y 0‖ ^ 2) ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (x := 1 + ‖(2 : ℂ) * y 0‖ ^ 2) (by positivity)
    linarith
  have h3 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (x := 4) (by norm_num)
    linarith
  unfold cpF
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem cpR_chart (j : Fin 2) (y : Fin 1 → ℂ) (hy : y ∈ ball (0 : Fin 1 → ℂ) 1 \ coordDiv (cpS j)) :
    cpR ((sChart j).symm y) = Real.exp 1 + cpF j y + ∑ i ∈ cpS j, Real.log (‖y i‖ ^ 2)⁻¹ := by
  fin_cases j
  · have hy0 : y 0 ≠ 0 := by
      intro h
      exact hy.2 ⟨0, by simp [cpS], h⟩
    simp only [cpR, cpF, cpS, sChart_symm_apply, Fin.zero_eta, Fin.isValue, Fin.val_zero, if_true,
      Finset.sum_singleton]
    rw [CP.chartCoord_chartInv_eq]
    have h10 : (Fin.succAbove (1 : Fin 2) 0) = 0 := rfl
    have hv1 : CP.chartVec 0 ((2 : ℂ) • y) 1 = 2 * y 0 := by
      rw [chartVec_zero_one]; simp
    simp only [h10, CP.chartVec_self, hv1]
    have hn : 0 < ‖y 0‖ := norm_pos_iff.mpr hy0
    have key : 1 + ‖1 / (2 * y 0)‖ ^ 2 = (1 + ‖(2 : ℂ) * y 0‖ ^ 2) / (4 * ‖y 0‖ ^ 2) := by
      rw [norm_div, norm_one, norm_mul]
      norm_num
      field_simp
      ring
    rw [key, Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_inv]
    ring
  · simp only [cpR, cpF, cpS, sChart_symm_apply, Fin.mk_one, Fin.isValue, Fin.val_one, one_ne_zero,
      if_false, Finset.sum_empty, add_zero, CP.chartCoord_chartInv]
    simp

def cpReg : RegChartData cpAtlas where
  toPotentialCharts := cpCharts
  S := cpS
  Yo := CP.chartDomain 1
  mem_Yo := cp_mem_Yo
  ph _ := 0
  ph_smooth _ := contDiffOn_const
  u_psh _ := by simpa [cpCharts] using isPsh_const _ (0 : ℝ)
  r := cpR
  one_le_r x _ := by
    have h1 : 0 ≤ Real.log (1 + ‖CP.chartCoord 1 x 0‖ ^ 2) := Real.log_nonneg (by nlinarith [norm_nonneg (CP.chartCoord 1 x 0)])
    have h2 := Real.add_one_le_exp (1 : ℝ)
    unfold cpR; linarith
  f := cpF
  f_smooth j := by
    unfold cpF
    split_ifs
    · exact (contDiff_logNormSq.sub contDiff_const).contDiffOn
    · exact contDiff_logNormSq.contDiffOn
  f_bdd := ⟨8, fun j y hy => cpF_bound j y hy⟩
  r_chart := cpR_chart
  Clog := 0
  Cph := 0
  ph_le _ _ := le_rfl
  ph_ge _ _ := by simp
  Cgrad := 0
  grad_le _ _ _ := by simp [cpCharts]

def cpBounded : BoundedPshData cpAtlas where
  toPotentialCharts := cpCharts
  ph _ := 0
  bdd := ⟨0, fun _ => by simp⟩
  u_psh _ := by simpa [cpCharts] using isPsh_const _ (0 : ℝ)

def cpBump : ContDiffBump (0 : Fin 1 → ℂ) := ⟨3 / 4, 13 / 16, by norm_num, by norm_num⟩

def cpEta (j : Fin 2) (x : CP 1) : ℝ := cpBump (sChart j x) - 1

theorem transition_contDiffOn (k j : Fin 2) :
    ContDiffOn ℝ ∞ (fun z => (2 : ℂ)⁻¹ • CP.chartCoord j (CP.chartInv k z))
      {z | CP.chartVec k z j ≠ 0} :=
  ((CP.contDiffOn_transition k j).restrict_scalars ℝ).const_smul _

theorem levi_ge_of_norm_le {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (y w : Fin D → ℂ) (M : ℝ)
    (h : ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ M) : -M * ‖w‖ ^ 2 ≤ levi φ y w := by
  set H := fderiv ℝ (fderiv ℝ φ) y with hH
  have hM : 0 ≤ M := (ContinuousLinearMap.opNorm_nonneg _).trans h
  have h1 : |H w w| ≤ M * ‖w‖ ^ 2 := by
    rw [← Real.norm_eq_abs]
    calc ‖H w w‖ ≤ ‖H‖ * ‖w‖ * ‖w‖ := H.le_opNorm₂ w w
      _ ≤ M * ‖w‖ * ‖w‖ := by gcongr
      _ = M * ‖w‖ ^ 2 := by ring
  have hIw : ‖Complex.I • w‖ = ‖w‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  have h2 : |H (Complex.I • w) (Complex.I • w)| ≤ M * ‖w‖ ^ 2 := by
    rw [← Real.norm_eq_abs]
    calc ‖H (Complex.I • w) (Complex.I • w)‖ ≤ ‖H‖ * ‖Complex.I • w‖ * ‖Complex.I • w‖ :=
          H.le_opNorm₂ _ _
      _ ≤ M * ‖w‖ * ‖w‖ := by rw [hIw]; gcongr
      _ = M * ‖w‖ ^ 2 := by ring
  have e : levi φ y w = (H w w + H (Complex.I • w) (Complex.I • w)) / 4 := rfl
  rw [e]
  have := neg_abs_le (H w w)
  have := neg_abs_le (H (Complex.I • w) (Complex.I • w))
  have : 0 ≤ M * ‖w‖ ^ 2 := by positivity
  linarith

theorem cpEta_hess_bound (j k : Fin 2) : ∃ M : ℝ, ∀ x ∈ cpMid j ∩ cpMid k,
    ‖fderiv ℝ (fderiv ℝ (cpEta j ∘ (sChart k).symm)) (sChart k x)‖ ≤ M := by
  set O := (sChart k).target ∩ (sChart k).symm ⁻¹' (sChart j).source with hOdef
  have hO : IsOpen O := (sChart k).isOpen_inter_preimage_symm (sChart j).open_source
  have hF : ContDiffOn ℝ ∞ (cpEta j ∘ (sChart k).symm) O := by
    have hlin : ContDiff ℝ ∞ (fun y : Fin 1 → ℂ => (2 : ℂ) • y) := contDiff_const_smul _
    have hT := (transition_contDiffOn k j).comp hlin.contDiffOn (s := O) (fun y hy => hy.2.1)
    exact (cpBump.contDiff.comp_contDiffOn hT).sub contDiffOn_const
  have hcont : ContinuousOn (fun y => fderiv ℝ (fderiv ℝ (cpEta j ∘ (sChart k).symm)) y) O :=
    (hF.fderiv_of_isOpen hO (m := 1) (by decide)).continuousOn_fderiv_of_isOpen hO le_rfl
  set K := sChart k '' (closure (cpMid j) ∩ closure (cpMid k)) with hKdef
  have hKc : IsCompact K :=
    (isClosed_closure.inter isClosed_closure).isCompact.image_of_continuousOn
      ((sChart k).continuousOn.mono fun x hx => cpCharts.closure_mid k hx.2)
  have hKO : K ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    have hxk : x ∈ (sChart k).source := cpCharts.closure_mid k hx.2
    refine ⟨(sChart k).map_source hxk, ?_⟩
    show (sChart k).symm (sChart k x) ∈ (sChart j).source
    rw [(sChart k).left_inv hxk]
    exact cpCharts.closure_mid j hx.1
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    (f := fun y => fderiv ℝ (fderiv ℝ (cpEta j ∘ (sChart k).symm)) y) (by exact hcont.mono hKO)
  exact ⟨M, fun x hx => hM _ ⟨x, ⟨subset_closure hx.1, subset_closure hx.2⟩, rfl⟩⟩

theorem sChart_norm_le_of_closure (j : Fin 2) (x : CP 1) (hx : x ∈ closure (cpMid j)) :
    x ∈ CP.chartDomain j ∧ ‖sChart j x‖ ≤ 7 / 8 := by
  have h := closure_region_subset j (c := 7 / 8) (by norm_num) (by norm_num) hx
  refine ⟨h.1, ?_⟩
  rw [norm_sChart]
  have := h.2
  linarith

theorem cpEta_smooth (j : Fin 2) : cpAtlas.SmoothOn (cpMid j) (cpEta j) := by
  intro k
  have hsub : (CP.chart k).target ∩ (CP.chart k).symm ⁻¹' cpMid j ⊆ {z | CP.chartVec k z j ≠ 0} :=
    fun z hz => hz.2.1.1
  exact (cpBump.contDiff.comp_contDiffOn ((transition_contDiffOn k j).mono hsub)).sub
    contDiffOn_const

theorem cpEta_bounds (j : Fin 2) (x : CP 1) : -1 ≤ cpEta j x ∧ cpEta j x ≤ 0 := by
  have h1 := cpBump.nonneg (x := sChart j x)
  have h2 := cpBump.le_one (x := sChart j x)
  simp only [cpEta]
  constructor <;> linarith

theorem cpEta_eq_zero (j : Fin 2) (x : CP 1) (hx : x ∈ cpInner j) : cpEta j x = 0 := by
  have h : ‖sChart j x‖ < 3 / 4 := by
    have := hx.2; rwa [mem_preimage, mem_ball_zero_iff] at this
  have h1 : cpBump (sChart j x) = 1 :=
    cpBump.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff]; exact h.le)
  simp [cpEta, h1]

theorem cpEta_eq_neg_one (j : Fin 2) (x : CP 1) (hx : x ∈ cpMid j \ closedReg j (13 / 8)) :
    cpEta j x = -1 := by
  have hxD : x ∈ CP.chartDomain j := hx.1.1.1
  have hgt : 13 / 8 < ‖CP.chartCoord j x‖ := by
    by_contra hle
    exact hx.2 ⟨hxD, not_lt.1 hle⟩
  have hn := norm_sChart j x
  have h0 : cpBump (sChart j x) = 0 := by
    apply cpBump.zero_of_le_dist
    rw [dist_zero_right]
    show (13 / 16 : ℝ) ≤ ‖sChart j x‖
    linarith
  simp [cpEta, h0]

theorem cpCutoff : ∃ Cη : ℝ, cpCharts.IsCutoffFamily cpEta Cη := by
  choose M hM using cpEta_hess_bound
  refine ⟨∑ j, ∑ k, |M j k|, fun j => cpEta_smooth j, fun j x _ => cpEta_bounds j x,
    fun j x hx => cpEta_eq_zero j x hx, fun j => ⟨closedReg j (13 / 8),
      isClosed_closedReg j (by norm_num), closedReg_subset_region j (by norm_num) (by norm_num),
      fun x hx => cpEta_eq_neg_one j x hx⟩, ?_⟩
  intro j k x hx w
  refine le_trans ?_ (levi_ge_of_norm_le _ _ w _ (hM j k x hx))
  have hle : M j k ≤ ∑ j, ∑ k, |M j k| :=
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun k => |M j k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans (Finset.single_le_sum (f := fun j => ∑ k, |M j k|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)))
  have : 0 ≤ ‖w‖ ^ 2 := by positivity
  nlinarith

theorem cpReg_trunc_zero (j : Fin cpReg.N) : cpReg.trunc 0 j = fun _ => 0 := by
  funext y
  have hc : (fun y => max (cpReg.u j y) (-0)) = fun _ => (0 : ℝ) :=
    funext fun y => by simp [RegChartData.u, PotentialCharts.chartFun, cpReg, cpCharts]
  unfold RegChartData.trunc limsupExt
  rw [hc]
  split_ifs
  · exact limsup_zero_real _
  · rfl

theorem cpReg_phReg (ρ : Mollifier 1) (t : ℝ) (j : Fin cpReg.N) (x : CP 1) : cpReg.phReg ρ 0 t j x = 0 := by
  simp only [RegChartData.phReg, RegChartData.smoothed, ReciprocityTheory.AnForm.A.molli]
  rw [cpReg_trunc_zero]
  simp [cpReg, cpCharts]

theorem cp_glueRegularised_hyp : ∃ (ρ : Mollifier 1) (Cη : ℝ),
    cpReg.IsCutoffFamily cpEta Cη ∧ (0 : ℝ) < 1 / 16 ∧ (0 : ℝ) < 1 ∧
    (∀ j, ∀ x ∈ closure (cpReg.mid j), closedBall (cpReg.chart j x) (1 / 16) ⊆ (cpReg.chart j).target) ∧
    (∀ j k, ∀ x ∈ cpReg.mid j ∩ cpReg.mid k,
      |cpReg.phReg ρ 0 (1 / 16) j x - cpReg.phReg ρ 0 (1 / 16) k x| ≤ 1) := by
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1
  obtain ⟨Cη, hη⟩ := cpCutoff
  refine ⟨ρ, Cη, hη, by norm_num, by norm_num, fun j x hx y hy => ?_, fun j k x _ => ?_⟩
  · have h := (sChart_norm_le_of_closure j x hx).2
    show y ∈ ball 0 1
    rw [mem_ball_zero_iff]
    have h1 : ‖y‖ ≤ ‖y - sChart j x‖ + ‖sChart j x‖ := norm_le_norm_sub_add y (sChart j x)
    have h2 : ‖y - sChart j x‖ ≤ 1 / 16 := by rw [← dist_eq_norm]; exact hy
    show ‖y‖ < 1
    linarith
  · rw [cpReg_phReg, cpReg_phReg]
    norm_num

theorem cp_hypotheses : CompactSpace (CP 1) ∧ T2Space (CP 1) ∧ Nonempty (RegChartData cpAtlas) ∧
    Nonempty (BoundedPshData cpAtlas) ∧ Nonempty (Mollifier 1) ∧
    ∃ Cη : ℝ, cpReg.IsCutoffFamily cpEta Cη :=
  ⟨inferInstance, inferInstance, ⟨cpReg⟩, ⟨cpBounded⟩, ReciprocityTheory.AnForm.A.mollifierInhabit_thm 1,
    cpCutoff⟩

end ProjectiveLine

end

end GroundTheory.Heights₂.Heights.Regular
