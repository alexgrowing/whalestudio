import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import ReciprocityTheory.ThetaSummability.TailSumEstimates.ConeExp

noncomputable section

namespace PositivityTheory.ThKEst.Sq

open scoped ENNReal
open MeasureTheory Finset PositivityTheory.ThKEst

theorem cone_exponent_bound_holds : ConeExp := by
  intro r c hc
  have h1 := ReciprocityTheory.ThetaSummability.Est.integrableOn_exp_logCone (0 : ℝ) (s := c) fun k => by
    have := hc (k.val + 1) (by omega) k.isLt
    unfold psum at this
    unfold ReciprocityTheory.ThetaSummability.Est.partialSum
    rw [Finset.sum_filter]
    simpa only [Nat.lt_succ_iff, Fin.le_def] using this
  have h2 : Cone r ⊆ ReciprocityTheory.ThetaSummability.Est.logCone r 0 := fun t ht k => by
    unfold ReciprocityTheory.ThetaSummability.Est.gap
    split_ifs with h
    · exact sub_nonneg.2 (ht.1 (by simp [Fin.le_def]))
    · simpa using ht.2 k
  refine (lintegral_mono_set h2).trans_lt ?_
  have h3 := h1.2
  rwa [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)] at h3

def ext {y : ℕ} (t : Fin y → ℝ) (j : ℕ) : ℝ := if h : j < y then t ⟨j, h⟩ else 0

theorem sum_ext {y N : ℕ} (hN : y ≤ N) (t : Fin y → ℝ) (g : ℕ → ℝ → ℝ) (hg : ∀ j, g j 0 = 0) :
    ∑ j : Fin y, g j (t j) = ∑ j ∈ range N, g j (ext t j) := by
  rw [← Finset.sum_subset (Finset.range_mono hN) fun j _ hj => by
    rw [ext, dif_neg (by simpa using hj), hg], ← Fin.sum_univ_eq_sum_range (fun j => g j (ext t j))]
  exact Finset.sum_congr rfl fun j _ => by simp [ext]

theorem sum_cut {q N : ℕ} (hN : q ≤ N) (g : ℕ → ℝ) :
    ∑ j : Fin q, g j = ∑ j ∈ range N, if j < q then g j else 0 := by
  rw [Fin.sum_univ_eq_sum_range g, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [mem_range, mem_filter]
  omega

theorem ext_nonneg {y : ℕ} {t : Fin y → ℝ} (ht : t ∈ Cone y) (j : ℕ) : 0 ≤ ext t j := by
  unfold ext
  split_ifs
  · exact ht.2 _
  · exact le_rfl

theorem ext_anti {y : ℕ} {t : Fin y → ℝ} (ht : t ∈ Cone y) : Antitone (ext t) := by
  intro i j hij
  by_cases hj : j < y
  · rw [ext, ext, dif_pos hj, dif_pos (by omega)]
    exact ht.1 (by simpa [Fin.le_def] using hij)
  · rw [ext, dif_neg hj]
    exact ext_nonneg ht i

theorem coneAff (r : ℕ) (a b : ℝ) (h : ∀ k : ℕ, 1 ≤ k → k ≤ r → a + b * ((k : ℝ) - 1) / 2 < 0) :
    ∫⁻ t in Cone r, ENNReal.ofReal (Real.exp (∑ i : Fin r, (a + b * (i.val : ℝ)) * t i)) < ⊤ := by
  refine cone_exponent_bound_holds r _ fun k hk hkr => ?_
  have e : psum (fun i : Fin r => a + b * (i.val : ℝ)) k = k * (a + b * ((k : ℝ) - 1) / 2) := by
    unfold psum
    rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then a + b * (j : ℝ) else 0), ← sum_cut hkr (fun j => a + b * (j : ℝ)),
      Fin.sum_univ_eq_sum_range (fun j => a + b * (j : ℝ))]
    clear h hk hkr
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [e]
  exact mul_neg_of_pos_of_neg (by exact_mod_cast hk) (h k hk hkr)

theorem square_integrable_integral_holds : ConeIntegralsFinite := by
  intro n d q y D hD h1 h2
  constructor
  · refine lt_of_eq_of_lt (lintegral_congr fun s => ?_) (coneAff q (D * (d / 2 - n + 1)) (2 * D) fun k hk hkq => ?_)
    · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      simp only [rho2, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rcases h1 with h1 | h1
      · omega
      · have a1 : (d : ℝ) + 2 * k < 2 * n := by exact_mod_cast (by omega : d + 2 * k < 2 * n)
        nlinarith
  · refine lt_of_eq_of_lt (lintegral_congr fun s => ?_) (coneAff y (D * (n - d + 1)) (2 * D) fun k hk hkq => ?_)
    · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      simp only [rho2, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rcases h2 with h2 | h2
      · omega
      · have a1 : (n : ℝ) + k < d := by exact_mod_cast (by omega : n + k < d)
        nlinarith

theorem posWt_eq (n d : ℕ) {q y : ℕ} (s : Fin q → ℝ) (t : Fin y → ℝ) :
    posWt n d s t = d * ∑ i, s i + n * ∑ j, t j - 2 * ∑ i, ∑ j, min (s i) (t j) := by
  have e : ∑ i, ∑ j, 2 * max (s i) (t j) =
      2 * y * ∑ i, s i + 2 * q * ∑ j, t j - 2 * ∑ i, ∑ j, min (s i) (t j) := by
    have : ∀ i j, 2 * max (s i) (t j) = 2 * s i + 2 * t j - 2 * min (s i) (t j) := fun i j => by
      linarith [min_add_max (s i) (t j)]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [posWt, e]
  ring

theorem posWt' : PosWt := by
  intro n d q y s t hs ht
  have hb : BddAbove (Set.range fun i : Fin (q + 1) => psum s i.val - psum t i.val) := (Set.finite_range _).bddAbove
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · rw [posWt_eq]
    have : 0 ≤ ∑ i, ∑ j, min (s i) (t j) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => le_min (hs.2 i) (ht.2 j)
    linarith
  · have := le_ciSup hb 0
    refine le_trans (le_of_eq ?_) this
    simp [psum]
  · have := le_ciSup hb ⟨i, by omega⟩
    unfold viol
    linarith

theorem exists_initial {q : ℕ} (P : Fin q → Prop) (hP : ∀ i i', i ≤ i' → P i' → P i) :
    ∃ k ≤ q, ∀ i, P i ↔ i.val < k := by
  classical
  have hex : ∃ k, ∀ h : k < q, ¬ P ⟨k, h⟩ := ⟨q, fun h => absurd h (lt_irrefl q)⟩
  refine ⟨Nat.find hex, Nat.find_min' hex fun h => absurd h (lt_irrefl q), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · by_contra h
    have h' : Nat.find hex ≤ i.val := not_lt.1 h
    exact Nat.find_spec hex (h'.trans_lt i.isLt) (hP _ i h' hi)
  · have := Nat.find_min hex hi
    push Not at this
    exact this.2

theorem major_slack {q : ℕ} {s t : Fin q → ℝ} (hs : s ∈ Cone q) (ht : t ∈ Cone q) {δ : ℝ}
    (h : ∀ i ≤ q, psum s i ≤ psum t i + δ) :
    ∑ i, ∑ j, min (s i) (s j) - ∑ i, ∑ j, min (s i) (t j) ≤ ∑ j : Fin q, ((q : ℝ) - 1 - j.val) * t j + q * δ := by
  classical
  have h1 : ∑ i, ∑ j, min (s i) (s j) - ∑ i, ∑ j, min (s i) (t j) ≤
      ∑ j, ∑ i, ((if t j < s i then s i else 0) - if t j < s i then t j else 0) := by
    rw [Finset.sum_comm (f := fun j i => (if t j < s i then s i else 0) - if t j < s i then t j else 0),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have := min_le_left (s i) (s j)
    split_ifs with hij
    · rw [min_eq_right hij.le]; linarith
    · rw [min_eq_left (not_lt.1 hij)]; linarith
  have h2 : ∀ j, ∑ i, ((if t j < s i then s i else 0) - if t j < s i then t j else 0) ≤
      ∑ i, (if i < j then t i else 0) + δ := by
    intro j
    obtain ⟨k, hk, hP⟩ := exists_initial (fun i => t j < s i) fun i i' hi h' => h'.trans_le (hs.1 hi)
    have a1 := h k hk
    unfold psum at a1
    simp only [hP]
    rw [Finset.sum_sub_distrib]
    have a2 : ∑ i : Fin q, (if i.val < k then t i else 0) - ∑ i : Fin q, (if i.val < k then t j else 0) ≤
        ∑ i, (if i < j then t i else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have := ht.2 i
      have := ht.2 j
      split_ifs with b1 b2 b2
      · linarith
      · linarith [ht.1 (not_lt.1 b2)]
      · linarith
      · linarith
    linarith
  refine h1.trans ((Finset.sum_le_sum fun j _ => h2 j).trans (le_of_eq ?_))
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul,
      Nat.cast_sub (by have := i.isLt; omega), Nat.cast_sub (by have := i.isLt; omega)]
    simp
  · simp

theorem majorant_inequality_holds : Major := fun q s t hs ht h => by
  simpa using major_slack hs ht (δ := 0) (by simpa using h)

theorem sum_min_self {q : ℕ} {s : Fin q → ℝ} (hs : s ∈ Cone q) :
    ∑ i, ∑ j, min (s i) (s j) = ∑ i : Fin q, (2 * (i.val : ℝ) + 1) * s i := by
  have e : ∀ i j, min (s i) (s j) = (if j ≤ i then s i else 0) + if i < j then s j else 0 := fun i j => by
    rcases le_or_gt j i with h | h
    · rw [if_pos h, if_neg (not_lt.2 h), add_zero, min_eq_left (hs.1 h)]
    · rw [if_neg (not_le.2 h), if_pos h, zero_add, min_eq_right (hs.1 h.le)]
  simp only [e, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then s j else 0), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const, Finset.filter_ge_eq_Iic,
    Finset.filter_gt_eq_Iio, Fin.card_Iic, Fin.card_Iio, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem exponent_bound_orthogonal_case : ExpSo := by
  intro n d q y Y hq hy hY hd
  refine ⟨d + q + 1, fun s hs t ht => ?_⟩
  obtain ⟨-, hδ, hps⟩ := posWt' n d q y s t hs ht
  set δ := viol s t
  let u : Fin q → ℝ := fun j => ext t j
  have hu : u ∈ Cone q := ⟨fun i j hij => ext_anti ht hij, fun j => ext_nonneg ht j⟩
  have hpu : ∀ k ≤ q, psum t k = psum u k := fun k hk => by
    unfold psum
    rw [sum_ext (Nat.le_add_left y q) t (fun j x => if j < k then x else 0) (by simp),
      sum_cut (Nat.le_add_right q y) (fun j => if j < k then ext t j else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> first | rfl | omega
  have h1 := major_slack hs hu (δ := δ) fun i hi => by rw [← hpu i hi]; exact hps i hi
  have h2 : ∑ i, ∑ j, min (s i) (u j) ≤ ∑ i, ∑ j, min (s i) (t j) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [sum_ext (Nat.le_add_left y q) t (fun _ x => min (s i) x) (fun _ => min_eq_right (hs.2 i)),
      sum_cut (Nat.le_add_right q y) (fun j => min (s i) (ext t j))]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · exact le_rfl
    · exact le_min (hs.2 i) (ext_nonneg ht j)
  have h3 : ∑ i, s i ≤ ∑ j, u j + δ := by
    have := hps q le_rfl
    rw [hpu q le_rfl] at this
    simpa [psum] using this
  have hn : 2 * (Y : ℝ) + 2 ≤ n := by exact_mod_cast hY
  have hd' : 2 * (n : ℝ) ≤ d := by exact_mod_cast hd
  have hq' : (q : ℝ) ≤ Y := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set c : ℝ := d / 2 - n + 1 / (4 * (q + 1)) with hc
  have hc1 : 1 / (4 * ((q : ℝ) + 1)) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hc2 : 0 ≤ 1 / (4 * ((q : ℝ) + 1)) := by positivity
  have h4 : ∑ j : Fin q, (c + ((q : ℝ) - 1 - j.val)) * u j ≤
      ∑ j : Fin y, (((d : ℝ) - 2 * j.val - 1) / 2 - n / 2 - 1 / 4) * t j := by
    rw [sum_ext (Nat.le_add_left y q) t (fun j x => (((d : ℝ) - 2 * j - 1) / 2 - n / 2 - 1 / 4) * x) (by simp),
      sum_cut (Nat.le_add_right q y) (fun j => (c + ((q : ℝ) - 1 - j)) * ext t j)]
    refine Finset.sum_le_sum fun j _ => ?_
    have a0 := ext_nonneg ht j
    split_ifs with hj
    · exact mul_le_mul_of_nonneg_right (by linarith) a0
    · by_cases hjy : j < y
      · have : (j : ℝ) + 1 ≤ Y := by exact_mod_cast (by omega : j + 1 ≤ Y)
        exact mul_nonneg (by linarith) a0
      · rw [ext, dif_neg hjy, mul_zero]
  have e1 : rho2 n s = n * ∑ i, s i - ∑ i, ∑ j, min (s i) (s j) := by
    rw [sum_min_self hs, rho2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j : Fin y, (((d : ℝ) - 2 * j.val - 1) / 2 - n / 2 - 1 / 4) * t j =
      rho2 d t / 2 - n / 2 * ∑ j, t j - (∑ j, t j) / 4 := by
    rw [rho2, Finset.sum_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ j : Fin q, (c + ((q : ℝ) - 1 - j.val)) * u j =
      c * ∑ j, u j + ∑ j : Fin q, ((q : ℝ) - 1 - j.val) * u j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : (∑ i, s i) / (4 * ((q : ℝ) + 1)) = 1 / (4 * ((q : ℝ) + 1)) * ∑ i, s i := by ring
  have hc0 : 0 ≤ c := by linarith
  have h5 := mul_le_mul_of_nonneg_left h3 hc0
  have h6 : c * δ ≤ (d + 1) * δ := mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) n]) hδ
  have e5 : c * ∑ i, s i = (d / 2 - n) * ∑ i, s i + 1 / (4 * ((q : ℝ) + 1)) * ∑ i, s i := by rw [hc]; ring
  rw [posWt_eq, e1, e4]
  rw [e2, e3] at h4
  nlinarith

end PositivityTheory.ThKEst.Sq
