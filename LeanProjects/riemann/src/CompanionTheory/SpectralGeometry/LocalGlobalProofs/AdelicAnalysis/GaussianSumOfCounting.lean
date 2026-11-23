import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic

noncomputable def wt (c : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else Real.exp (-(c * 4 ^ j / 4))

lemma wt_nonneg (c : ℝ) (j : ℕ) : 0 ≤ wt c j := by
  unfold wt; split_ifs
  · exact zero_le_one
  · exact (Real.exp_pos _).le

lemma exists_dyadic {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    ∃ j : ℕ, u ≤ 2 ^ j ∧ Real.exp (-(c * u ^ 2)) ≤ wt c j := by
  classical
  have hex : ∃ j : ℕ, u ≤ 2 ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt u (one_lt_two : (1 : ℝ) < 2)
    exact ⟨j, hj.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases hj : Nat.find hex with _ | k
  · simp only [wt, if_true]
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c * u ^ 2 := by positivity
    linarith
  · have hlt : ¬ u ≤ 2 ^ k := Nat.find_min hex (by omega)
    push_neg at hlt
    have hsq : (4 : ℝ) ^ k ≤ u ^ 2 := by
      have h1 : ((2 : ℝ) ^ k) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hlt.le 2
      have h2 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      linarith
    simp only [wt, Nat.succ_ne_zero, if_false]
    apply Real.exp_le_exp.mpr
    have h3 : c * 4 ^ (k + 1) / 4 = c * 4 ^ k := by rw [pow_succ]; ring
    rw [h3]
    have := mul_le_mul_of_nonneg_left hsq hc.le
    linarith

lemma summable_wt {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Summable fun j : ℕ => wt c j * ((4 : ℝ) ^ n) ^ j := by
  set K : ℝ := ((n + 1).factorial : ℝ) * (4 / c) ^ (n + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hgeo : Summable fun j : ℕ => (K + 1) * ((1 : ℝ) / 4) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (wt_nonneg c j) (by positivity)) ?_ hgeo
  intro j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [wt]; linarith
  · have hj0 : j ≠ 0 := by omega
    simp only [wt, hj0, if_false]
    set y : ℝ := 4 ^ j with hy
    have hy0 : 0 < y := by positivity
    have hx0 : 0 ≤ c * y / 4 := by positivity
    have hb := Real.pow_div_factorial_le_exp (c * y / 4) hx0 (n + 1)
    have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
    have hxp : 0 < (c * y / 4) ^ (n + 1) := by positivity
    have hexp : Real.exp (-(c * y / 4)) ≤ ((n + 1).factorial : ℝ) / (c * y / 4) ^ (n + 1) := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      exact hb
    have hswap : ((4 : ℝ) ^ n) ^ j = y ^ n := by rw [hy, ← pow_mul, ← pow_mul, mul_comm]
    rw [hswap]
    calc Real.exp (-(c * y / 4)) * y ^ n
        ≤ ((n + 1).factorial : ℝ) / (c * y / 4) ^ (n + 1) * y ^ n :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = K * (1 / 4) ^ j := by
          have : ((1 : ℝ) / 4) ^ j = y⁻¹ := by rw [hy, one_div, inv_pow]
          rw [this, hK, div_pow, div_pow, mul_pow, pow_succ y n]
          field_simp
      _ ≤ (K + 1) * (1 / 4) ^ j := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

lemma radius_bound (n j : ℕ) {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    (2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n) ≤
      ((4 : ℝ) ^ n) ^ j * ((1 + (Real.sqrt t₀ ^ n)⁻¹) * (Real.sqrt t ^ n)⁻¹) := by
  have hs₀ : 0 < Real.sqrt t₀ := Real.sqrt_pos.mpr ht₀
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr (ht₀.trans_le ht)
  have hle : Real.sqrt t₀ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  set A : ℝ := ((2 : ℝ) ^ j) ^ n with hA
  set B : ℝ := (Real.sqrt t ^ n)⁻¹ with hB
  set B₀ : ℝ := (Real.sqrt t₀ ^ n)⁻¹ with hB₀
  have hA1 : 1 ≤ A := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hBpos : 0 < B := by positivity
  have hBB : B ≤ B₀ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hs₀.le hle n)
  have e1 : (2 ^ j / Real.sqrt t) ^ n = A * B := by
    rw [div_pow, hA, hB, div_eq_mul_inv]
  have e2 : (2 ^ j / Real.sqrt t) ^ (2 * n) = (A * B) ^ 2 := by
    rw [mul_comm 2 n, pow_mul, e1]
  have e3 : ((4 : ℝ) ^ n) ^ j = A ^ 2 := by
    rw [hA, ← pow_mul, ← pow_mul, ← pow_mul]
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, ← pow_mul]; congr 1; ring
  rw [e1, e2, e3]
  have h1 : A * B ≤ A ^ 2 * B := by
    apply mul_le_mul_of_nonneg_right _ hBpos.le
    nlinarith
  have h2 : (A * B) ^ 2 ≤ A ^ 2 * (B₀ * B) := by
    have : (A * B) ^ 2 = A ^ 2 * (B * B) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right hBB hBpos.le
  nlinarith

lemma gaussian_le_tsum {X : Type} (c t : ℝ) (hc : 0 < c) (ht : 0 < t) (s : X → ℝ) (p : X → Prop)
    (hs : ∀ x, 0 ≤ s x) (x : X) :
    Set.indicator {x | p x} (fun x => ENNReal.ofReal (Real.exp (-(c * t * s x ^ 2)))) x ≤
      ∑' j : ℕ, ENNReal.ofReal (wt c j) *
        Set.indicator {x | p x ∧ s x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
  classical
  by_cases hp : p x
  · have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    obtain ⟨j, hj, hexp⟩ := exists_dyadic (c := c) (u := Real.sqrt t * s x) hc
      (mul_nonneg hq.le (hs x))
    have hmem : x ∈ {x | p x ∧ s x ≤ 2 ^ j / Real.sqrt t} :=
      ⟨hp, by rw [le_div_iff₀ hq, mul_comm]; exact hj⟩
    have heq : c * (Real.sqrt t * s x) ^ 2 = c * t * s x ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ht.le]; ring
    rw [heq] at hexp
    rw [Set.indicator_of_mem (show x ∈ {x | p x} from hp)]
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem hmem, mul_one]
    exact ENNReal.ofReal_le_ofReal hexp
  · rw [Set.indicator_of_notMem (show x ∉ {x | p x} from hp)]
    exact zero_le

theorem gaussian_sum_le (n : ℕ) (c t₀ C : ℝ) (hc : 0 < c) (ht₀ : 0 < t₀) :
    ∀ (X Ω : Type) [MeasurableSpace Ω] [Countable X] (Pr : Measure Ω)
      (s : Ω → X → ℝ) (p : Ω → X → Prop), (∀ x, Measurable fun ω => s ω x) →
      (∀ x, MeasurableSet {ω | p ω x}) → (∀ ω x, 0 ≤ s ω x) →
      (∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ R}
          (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤ ENNReal.ofReal (C * (R ^ n + R ^ (2 * n)))) →
      ∀ t : ℝ, t₀ ≤ t → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x}
          (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ∂Pr ≤
        ENNReal.ofReal ((|C| * (1 + (Real.sqrt t₀ ^ n)⁻¹) *
          ∑' j : ℕ, wt c j * ((4 : ℝ) ^ n) ^ j) * (Real.sqrt t ^ n)⁻¹) := by
  intro X Ω _ _ Pr s p hsm hpm hs0 hcount t ht
  have htpos : 0 < t := ht₀.trans_le ht
  have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  set B : ℝ := (Real.sqrt t ^ n)⁻¹ with hB
  set D : ℝ := 1 + (Real.sqrt t₀ ^ n)⁻¹ with hD
  have hB0 : 0 ≤ B := by positivity
  have hD0 : 0 ≤ D := by positivity
  set E : ℝ := |C| * D * B with hE
  have hE0 : 0 ≤ E := by positivity
  have hmeas : ∀ j : ℕ, Measurable fun ω => ∑' x, Set.indicator
      {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
    intro j
    refine Measurable.ennreal_tsum fun x => ?_
    have hset : MeasurableSet {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} :=
      (hpm x).inter (measurableSet_le (hsm x) measurable_const)
    have heq : (fun ω => Set.indicator {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t}
        (fun _ => (1 : ℝ≥0∞)) x) =
        Set.indicator {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      classical
      by_cases h : p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t
      · rw [Set.indicator_of_mem (show x ∈ {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h),
          Set.indicator_of_mem (show ω ∈ {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h)]
      · rw [Set.indicator_of_notMem (show x ∉ {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h),
          Set.indicator_of_notMem (show ω ∉ {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h)]
    rw [heq]
    exact measurable_const.indicator hset
  have hpt : ∀ ω, ∑' x, Set.indicator {x | p ω x}
      (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ≤
      ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
        {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
    intro ω
    calc _ ≤ ∑' x, ∑' j : ℕ, ENNReal.ofReal (wt c j) * Set.indicator
            {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x :=
          ENNReal.tsum_le_tsum fun x =>
            gaussian_le_tsum c t hc htpos (s ω) (p ω) (hs0 ω) x
      _ = ∑' j : ℕ, ∑' x, ENNReal.ofReal (wt c j) * Set.indicator
            {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x :=
          ENNReal.tsum_comm
      _ = _ := by simp_rw [ENNReal.tsum_mul_left]
  have hterm : ∀ j : ℕ, ENNReal.ofReal (wt c j) * ∫⁻ ω, ∑' x, Set.indicator
      {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤
      ENNReal.ofReal (wt c j * ((4 : ℝ) ^ n) ^ j * E) := by
    intro j
    have hR : (0 : ℝ) < 2 ^ j / Real.sqrt t := by positivity
    have hr := radius_bound n j ht₀ ht
    have hb : C * ((2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n)) ≤
        ((4 : ℝ) ^ n) ^ j * E := by
      have h0 : 0 ≤ (2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n) := by positivity
      calc _ ≤ |C| * ((2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n)) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) h0
        _ ≤ |C| * (((4 : ℝ) ^ n) ^ j * (D * B)) :=
            mul_le_mul_of_nonneg_left hr (abs_nonneg C)
        _ = _ := by rw [hE]; ring
    calc _ ≤ ENNReal.ofReal (wt c j) * ENNReal.ofReal (((4 : ℝ) ^ n) ^ j * E) := by
          gcongr
          exact (hcount _ hR).trans (ENNReal.ofReal_le_ofReal hb)
      _ = _ := by
          rw [← ENNReal.ofReal_mul (wt_nonneg c j), mul_assoc]
  have hsum : Summable fun j : ℕ => wt c j * ((4 : ℝ) ^ n) ^ j * E :=
    (summable_wt hc n).mul_right E
  calc _ ≤ ∫⁻ ω, ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr :=
        lintegral_mono hpt
    _ = ∑' j : ℕ, ∫⁻ ω, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr :=
        lintegral_tsum fun j => ((hmeas j).const_mul _).aemeasurable
    _ = ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∫⁻ ω, ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr := by
        congr 1; funext j
        exact lintegral_const_mul _ (hmeas j)
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (wt c j * ((4 : ℝ) ^ n) ^ j * E) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℕ, wt c j * ((4 : ℝ) ^ n) ^ j * E) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (mul_nonneg (wt_nonneg c j) (by positivity)) hE0) hsum).symm
    _ = _ := by
        rw [tsum_mul_right, hE]
        congr 1
        ring

theorem gaussian_sum_of_counting :
    ∀ (n : ℕ) (c t₀ C : ℝ), 0 < c → 0 < t₀ → ∃ C' : ℝ, ∀ (X Ω : Type) [MeasurableSpace Ω]
      [Countable X] (Pr : Measure Ω) (s : Ω → X → ℝ) (p : Ω → X → Prop),
      (∀ x, Measurable fun ω => s ω x) → (∀ x, MeasurableSet {ω | p ω x}) →
      (∀ ω x, 0 ≤ s ω x) →
      (∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ R}
          (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤ ENNReal.ofReal (C * (R ^ n + R ^ (2 * n)))) →
      ∀ t : ℝ, t₀ ≤ t → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x}
          (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ∂Pr ≤
        ENNReal.ofReal (C' * (Real.sqrt t ^ n)⁻¹) :=
  fun n c t₀ C hc ht₀ => ⟨_, gaussian_sum_le n c t₀ C hc ht₀⟩

end GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
