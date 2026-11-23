import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape

noncomputable section

open MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.SlabGlue

open PositivityTheory.Rg.Rs.An

theorem tsum_pi_prod_ne_top : ∀ (m : ℕ) (f : Fin m → ℕ → ℝ≥0∞), (∀ j, ∑' k, f j k ≠ ⊤) →
    ∑' s : Fin m → ℕ, ∏ j, f j (s j) ≠ ⊤ := by
  intro m
  induction m with
  | zero =>
    intro f _
    simp
  | succ m ih =>
    intro f hf
    have e : ∑' s : Fin (m + 1) → ℕ, ∏ j, f j (s j)
        = (∑' k, f 0 k) * ∑' s : Fin m → ℕ, ∏ j : Fin m, f j.succ (s j) := by
      rw [← (Fin.consEquiv fun _ : Fin (m + 1) => ℕ).tsum_eq, ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
      refine tsum_congr fun k => ?_
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun s => ?_
      simp [Fin.prod_univ_succ]
    rw [e]
    exact ENNReal.mul_ne_top (hf 0) (ih _ fun j => hf j.succ)

theorem tsum_exp_ne_top {a : ℝ} (ha : a < 0) :
    ∑' k : ℕ, ENNReal.ofReal (Real.exp (a * k)) ≠ ⊤ := by
  have h : Summable fun k : ℕ => Real.exp (a * k) := by
    have := Real.summable_exp_nat_mul_iff.2 ha
    simpa [mul_comm] using this
  exact h.tsum_ofReal_ne_top

theorem sr_add {n : ℕ} (x y : Fin n → ℝ) (r : ℕ) : sr (x + y) r = sr x r + sr y r := by
  unfold sr
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

def part (n : ℕ) (c : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin (n - 1), if (i : ℕ) ≤ j then c j else 0

theorem sr_part {n : ℕ} (c : Fin (n - 1) → ℝ) (j : Fin (n - 1)) :
    sr (part n c) ((j : ℕ) + 1) = c j := by
  have hj := j.2
  unfold sr
  rw [dif_pos (by omega : 0 < (j : ℕ) + 1 ∧ (j : ℕ) + 1 < n)]
  simp only [part, ← Finset.sum_sub_distrib, Nat.add_sub_cancel]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ j := fun h => hb (Fin.ext h)
    by_cases h1 : (j : ℕ) ≤ b
    · have h2 : (j : ℕ) + 1 ≤ b := by omega
      simp [h1, h2]
    · have h2 : ¬ (j : ℕ) + 1 ≤ b := by omega
      simp [h1, h2]
  · simp

theorem part_last {n : ℕ} (c : Fin (n - 1) → ℝ) (i : Fin n) (hi : (i : ℕ) + 1 = n) :
    part n c i = 0 := by
  unfold part
  refine Finset.sum_eq_zero fun j _ => ?_
  have := j.2
  rw [if_neg (by omega)]

theorem y_bound {n : ℕ} (y : Fin n → ℝ) (hl : ∀ i : Fin n, (i : ℕ) + 1 = n → 0 ≤ y i ∧ y i ≤ 1)
    (hd : ∀ j : Fin (n - 1), 0 ≤ sr y ((j : ℕ) + 1) ∧ sr y ((j : ℕ) + 1) ≤ 1) :
    ∀ (d : ℕ) (i : Fin n), (i : ℕ) + 1 + d = n → 0 ≤ y i ∧ y i ≤ d + 1 := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simpa using hl i (by omega)
  | succ d ih =>
    intro i hi
    have hi' : (i : ℕ) + 1 < n := by omega
    obtain ⟨h1, h2⟩ := ih ⟨(i : ℕ) + 1, hi'⟩ (by simp only; omega)
    obtain ⟨h3, h4⟩ := hd ⟨(i : ℕ), by omega⟩
    have e : sr y ((i : ℕ) + 1) = y i - y ⟨(i : ℕ) + 1, hi'⟩ := by
      unfold sr
      rw [dif_pos (by omega : 0 < (i : ℕ) + 1 ∧ (i : ℕ) + 1 < n)]
      simp
    simp only at h3 h4
    rw [e] at h3 h4
    push_cast
    constructor <;> linarith

theorem abs_y_le {n : ℕ} (y : Fin n → ℝ) (hl : ∀ i : Fin n, (i : ℕ) + 1 = n → 0 ≤ y i ∧ y i ≤ 1)
    (hd : ∀ j : Fin (n - 1), 0 ≤ sr y ((j : ℕ) + 1) ∧ sr y ((j : ℕ) + 1) ≤ 1) (i : Fin n) :
    |y i| ≤ n := by
  have hi := i.2
  obtain ⟨h1, h2⟩ := y_bound y hl hd (n - 1 - i) i (by omega)
  rw [abs_of_nonneg h1]
  have : ((n - 1 - (i : ℕ) : ℕ) : ℝ) + 1 ≤ n := by
    have : n - 1 - (i : ℕ) + 1 ≤ n := by omega
    exact_mod_cast this
  linarith

theorem abs_sr_le {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, |y i| ≤ n) (r : ℕ) :
    |sr y r| ≤ 2 * n := by
  unfold sr
  split_ifs with h
  · have h1 := hy ⟨r - 1, by omega⟩
    have h2 := hy ⟨r, h.2⟩
    have := abs_sub (y ⟨r - 1, by omega⟩) (y ⟨r, h.2⟩)
    linarith
  · simp

theorem sum_range_sr {n : ℕ} (f : ℕ → ℝ) (x : Fin n → ℝ) :
    ∑ r ∈ Finset.range n, f r * sr x r = ∑ j : Fin (n - 1), f ((j : ℕ) + 1) * sr x ((j : ℕ) + 1) := by
  cases n with
  | zero => simp
  | succ m =>
    have h0 : sr x 0 = 0 := by simp [sr]
    rw [Finset.sum_range_succ', h0, mul_zero, add_zero, Finset.sum_range]
    rfl

theorem setLIntegral_le_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) (A : Set α) (c : ℝ≥0∞) (h : ∀ g ∈ A, f g ≤ c) :
    ∫⁻ g in A, f g ∂μ ≤ c * μ A := by
  have hB : MeasurableSet {g | f g ≤ c} := measurableSet_le hf measurable_const
  have hae : ∀ᵐ g ∂(μ.restrict A), f g ≤ c := by
    rw [ae_iff, show {a | ¬ f a ≤ c} = {g | f g ≤ c}ᶜ from rfl, Measure.restrict_apply hB.compl]
    have : {g | f g ≤ c}ᶜ ∩ A = ∅ := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false, not_and, not_not]
      intro h1 h2
      exact h1 (h g h2)
    rw [this, measure_empty]
  calc ∫⁻ g in A, f g ∂μ ≤ ∫⁻ _ in A, c ∂μ := lintegral_mono_ae hae
    _ = c * μ A := setLIntegral_const _ _

theorem slabGlue : SlabGlue := by
  intro hBV K _ _ n μ _ φ κ hφ hB hκ ω hω hωB t₀
  obtain ⟨Cv, hCv⟩ := hBV K n μ ω hω hωB
  obtain ⟨C, hC⟩ := hB ω hω hωB (|t₀| + 2 * n) (maxCompact (K := K) (n := n) : Set _)
    isCompact_maxCompact
  let box : (Fin n → ℝ) → Set (AdelicGLn.AdelicGL K n) := fun x =>
    {g | ∃ b ∈ ω, ∃ y : Fin n → ℝ, (∀ i, |y i| ≤ n) ∧ ∃ k ∈ maxCompact (K := K) (n := n),
      g = b * tor K (x + y) * k}
  let X : (Fin (n - 1) → ℕ) → Fin n → ℝ := fun s => part n fun j => -t₀ + s j
  let a : Fin (n - 1) → ℝ := fun j => 2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1))
  let E : ℝ := ∑ r ∈ Finset.range n, |κ r| * (2 * n)
  let D : ℝ := (max C 0 * Real.exp E) ^ 2 * Cv * Real.exp (-t₀ * ∑ j, a j)
  have ha : ∀ j, a j < 0 := by
    intro j
    have hj := j.2
    have := hκ ((j : ℕ) + 1) (by omega) (by omega)
    show 2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1)) < 0
    linarith
  have hXs : ∀ s (j : Fin (n - 1)), sr (X s) ((j : ℕ) + 1) = -t₀ + s j := fun s j => sr_part _ j

  have hcover : slab ω t₀ ⊆ ⋃ s, box (X s) := by
    rintro g ⟨b, hb, x, hx, hlast, k, hk, rfl⟩
    let s : Fin (n - 1) → ℕ := fun j => ⌊sr x ((j : ℕ) + 1) + t₀⌋₊
    refine Set.mem_iUnion.2 ⟨s, b, hb, x - X s, ?_, k, hk, ?_⟩
    · refine abs_y_le _ ?_ ?_
      · intro i hi
        have : X s i = 0 := part_last _ i hi
        simpa [this] using hlast i hi
      · intro j
        have e : sr x ((j : ℕ) + 1) = sr (X s) ((j : ℕ) + 1) + sr (x - X s) ((j : ℕ) + 1) := by
          rw [← sr_add, add_sub_cancel]
        rw [hXs] at e
        have h0 : 0 ≤ sr x ((j : ℕ) + 1) + t₀ := by
          have := hx ((j : ℕ) + 1)
          linarith
        have h1 : ((s j : ℕ) : ℝ) ≤ sr x ((j : ℕ) + 1) + t₀ := Nat.floor_le h0
        have h2 : sr x ((j : ℕ) + 1) + t₀ < (s j : ℕ) + 1 := Nat.lt_floor_add_one _
        constructor <;> linarith
    · rw [add_sub_cancel]

  have hbox : ∀ s, ∫⁻ g in box (X s), ‖φ g‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) := by
    intro s
    let S : ℝ := ∑ r ∈ Finset.range n, κ r * sr (X s) r
    let W : ℝ := max C 0 * Real.exp E * Real.exp S
    have hW0 : 0 ≤ W := by positivity
    have hnorm : ∀ g ∈ box (X s), ‖φ g‖ₑ ^ 2 ≤ ENNReal.ofReal (W ^ 2) := by
      rintro g ⟨b, hb, y, hy, k, hk, rfl⟩
      have hsr : ∀ r, -(|t₀| + 2 * n) ≤ sr (X s + y) r := by
        intro r
        by_cases hr : 0 < r ∧ r < n
        · rw [sr_add]
          have h1 : sr (X s) r = -t₀ + s ⟨r - 1, by omega⟩ := by
            have := hXs s ⟨r - 1, by omega⟩
            simp only at this
            rwa [Nat.sub_add_cancel hr.1] at this
          have h2 := abs_le.1 (abs_sr_le y hy r)
          have h3 : (0 : ℝ) ≤ (s ⟨r - 1, by omega⟩ : ℕ) := Nat.cast_nonneg _
          have h4 := le_abs_self t₀
          rw [h1]
          linarith [h2.1]
        · have : sr (X s + y) r = 0 := by simp [sr, hr]
          rw [this]
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
          have := abs_nonneg t₀
          linarith
      have h1 := hC b hb (X s + y) hsr k hk
      have h2 : ∑ r ∈ Finset.range n, κ r * sr (X s + y) r ≤ S + E := by
        show _ ≤ ∑ r ∈ Finset.range n, κ r * sr (X s) r + ∑ r ∈ Finset.range n, |κ r| * (2 * n)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun r _ => ?_
        rw [sr_add, mul_add]
        have h3 : κ r * sr y r ≤ |κ r| * (2 * n) := by
          calc κ r * sr y r ≤ |κ r * sr y r| := le_abs_self _
            _ = |κ r| * |sr y r| := abs_mul _ _
            _ ≤ |κ r| * (2 * n) := mul_le_mul_of_nonneg_left (abs_sr_le y hy r) (abs_nonneg _)
        linarith
      have h3 : ‖φ (b * tor K (X s + y) * k)‖ ≤ W := by
        calc _ ≤ C * Real.exp (∑ r ∈ Finset.range n, κ r * sr (X s + y) r) := h1
          _ ≤ max C 0 * Real.exp (∑ r ∈ Finset.range n, κ r * sr (X s + y) r) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
          _ ≤ max C 0 * Real.exp (S + E) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (le_max_right _ _)
          _ = W := by
              show _ = max C 0 * Real.exp E * Real.exp S
              rw [Real.exp_add]; ring
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h3 2)
    have hmeas : Measurable fun g => ‖φ g‖ₑ ^ 2 := (hφ.measurable.enorm).pow_const 2
    have hexp : W ^ 2 * (Cv * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r))
        = D * ∏ j, Real.exp (a j * s j) := by
      have e1 : ∑ r ∈ Finset.range n, κ r * sr (X s) r
          = ∑ j : Fin (n - 1), κ ((j : ℕ) + 1) * (-t₀ + s j) := by
        rw [sum_range_sr]
        exact Finset.sum_congr rfl fun j _ => by rw [hXs]
      have e2 : ∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r
          = ∑ j : Fin (n - 1), 2 * rho K n ((j : ℕ) + 1) * (-t₀ + s j) := by
        rw [sum_range_sr (fun r => 2 * rho K n r)]
        exact Finset.sum_congr rfl fun j _ => by rw [hXs]
      have e3 : 2 * S - ∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r
          = -t₀ * ∑ j, a j + ∑ j, a j * s j := by
        show 2 * ∑ r ∈ Finset.range n, κ r * sr (X s) r - _ = _
        rw [e1, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        show _ = -t₀ * (2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1)))
          + (2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1))) * s j
        ring
      have e4 : Real.exp S ^ 2 * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)
          = Real.exp (-t₀ * ∑ j, a j) * ∏ j, Real.exp (a j * s j) := by
        rw [← Real.exp_sum, ← Real.exp_add, ← e3, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
      show (max C 0 * Real.exp E * Real.exp S) ^ 2 * _ = (max C 0 * Real.exp E) ^ 2 * Cv * Real.exp (-t₀ * ∑ j, a j) * _
      calc _ = (max C 0 * Real.exp E) ^ 2 * Cv * (Real.exp S ^ 2 *
              Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)) := by ring
        _ = _ := by rw [e4]; ring
    calc ∫⁻ g in box (X s), ‖φ g‖ₑ ^ 2 ∂μ
        ≤ ENNReal.ofReal (W ^ 2) * μ (box (X s)) :=
          setLIntegral_le_of_bound μ hmeas _ _ hnorm
      _ ≤ ENNReal.ofReal (W ^ 2) * ENNReal.ofReal
            (Cv * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)) := by
          gcongr
          exact hCv (X s)
      _ = ENNReal.ofReal (D * ∏ j, Real.exp (a j * s j)) := by
          rw [← ENNReal.ofReal_mul (by positivity), hexp]
      _ = _ := by
          rw [ENNReal.ofReal_mul' (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le),
            ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le]
  have hsum : ∑' s : Fin (n - 1) → ℕ, ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) ≠ ⊤ :=
    tsum_pi_prod_ne_top (n - 1) (fun j k => ENNReal.ofReal (Real.exp (a j * k)))
      fun j => tsum_exp_ne_top (ha j)
  calc ∫⁻ g in slab ω t₀, ‖φ g‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ g in ⋃ s, box (X s), ‖φ g‖ₑ ^ 2 ∂μ := lintegral_mono_set hcover
    _ ≤ ∑' s, ∫⁻ g in box (X s), ‖φ g‖ₑ ^ 2 ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' s, ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) :=
        ENNReal.tsum_le_tsum hbox
    _ = ENNReal.ofReal D * ∑' s : Fin (n - 1) → ℕ, ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) :=
        ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hsum)

end GlobalTheory.CompanionTheory.SlabGlue

end
