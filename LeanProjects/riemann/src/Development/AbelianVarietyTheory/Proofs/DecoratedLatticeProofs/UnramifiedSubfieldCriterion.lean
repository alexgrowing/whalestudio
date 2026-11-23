import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK

noncomputable section

namespace GlobalTheory.SubKur

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM Filter Topology

section General

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_sub_le_max (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max x (-y)

theorem norm_sum_le {ι : Type} (s : Finset ι) (f : ι → K) {r : ℝ} (hr : 0 ≤ r) (h : ∀ i ∈ s, ‖f i‖ ≤ r) :
    ‖∑ i ∈ s, f i‖ ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem norm_pow_sub_pow_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  have hs : ‖∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)‖ ≤ 1 := by
    refine norm_sum_le _ _ zero_le_one fun i _ => ?_
    rw [norm_mul, norm_pow, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ha) (by positivity) (pow_le_one₀ (norm_nonneg _) hb)
  calc _ ≤ 1 * ‖a - b‖ := by gcongr
    _ = _ := one_mul _

theorem norm_pow_l_sub_le (l : ℕ) {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hab : ‖a - b‖ ≤ ‖(l : K)‖) :
    ‖a ^ l - b ^ l‖ ≤ ‖(l : K)‖ * ‖a - b‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  gcongr
  have hsplit : ∑ i ∈ Finset.range l, a ^ i * b ^ (l - 1 - i) =
      ∑ i ∈ Finset.range l, (a ^ i - b ^ i) * b ^ (l - 1 - i) + (l : K) * b ^ (l - 1) := by
    have h1 : ∀ i ∈ Finset.range l, a ^ i * b ^ (l - 1 - i) = (a ^ i - b ^ i) * b ^ (l - 1 - i) + b ^ (l - 1) := by
      intro i hi
      have hi' : i + (l - 1 - i) = l - 1 := by
        have := Finset.mem_range.1 hi
        omega
      rw [sub_mul, ← pow_add, hi']
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine norm_sum_le _ _ (norm_nonneg _) fun i _ => ?_
    rw [norm_mul, norm_pow]
    calc ‖a ^ i - b ^ i‖ * ‖b‖ ^ (l - 1 - i) ≤ ‖a - b‖ * 1 := by
          gcongr
          · exact norm_pow_sub_pow_le ha hb i
          · exact pow_le_one₀ (norm_nonneg _) hb
      _ ≤ _ := by rw [mul_one]; exact hab
  · rw [norm_mul, norm_pow]
    calc ‖(l : K)‖ * ‖b‖ ^ (l - 1) ≤ ‖(l : K)‖ * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hb
      _ = _ := mul_one _

theorem norm_pow_l_pow_sub_le (l : ℕ) (hl : ‖(l : K)‖ ≤ 1) {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hab : ‖a - b‖ ≤ ‖(l : K)‖) (m : ℕ) :
    ‖a ^ (l ^ m) - b ^ (l ^ m)‖ ≤ ‖(l : K)‖ ^ m * ‖a - b‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ha' : ‖a ^ (l ^ m)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
    have hb' : ‖b ^ (l ^ m)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb
    have hpm : ‖(l : K)‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) hl
    have hd : ‖a ^ (l ^ m) - b ^ (l ^ m)‖ ≤ ‖(l : K)‖ :=
      ih.trans ((mul_le_of_le_one_left (norm_nonneg _) hpm).trans hab)
    rw [pow_succ, pow_mul, pow_mul]
    calc _ ≤ ‖(l : K)‖ * ‖a ^ (l ^ m) - b ^ (l ^ m)‖ := norm_pow_l_sub_le l ha' hb' hd
      _ ≤ ‖(l : K)‖ * (‖(l : K)‖ ^ m * ‖a - b‖) := by gcongr
      _ = _ := by ring

end General

section Padic

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_lt_one : ‖(l : ℂ_[l])‖ < 1 := by
  have h : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_l_pos : 0 < ‖(l : ℂ_[l])‖ := by
  rw [norm_pos_iff]
  exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem mem_Kur_of_pow_eq {N : ℕ} (hN : 0 < N) {t : ℂ_[l]} (ht : t ^ (l ^ N) = t) : t ∈ MaximalUnramifiedExtension l := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact (MaximalUnramifiedExtension l).zero_mem
  have hp : l.Prime := Fact.out
  have hq1 : 2 ≤ l ^ N := le_trans hp.two_le (Nat.le_self_pow hN.ne' l)
  have hpow : t ^ (l ^ N - 1) = 1 := by
    have h2 : t ^ (l ^ N - 1) * t = 1 * t := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), ht, one_mul]
    exact mul_right_cancel₀ h0 h2
  have hnd : ¬ l ∣ l ^ N - 1 := by
    intro hd
    have h1 : l ∣ l ^ N := dvd_pow_self l hN.ne'
    have h3 : l ∣ l ^ N - (l ^ N - 1) := Nat.dvd_sub h1 hd
    rw [show l ^ N - (l ^ N - 1) = 1 by omega] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
  exact Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨l ^ N - 1, by omega, hnd, hpow⟩)

variable (F : Subfield ℂ_[l]) (N : ℕ)

theorem closure_res (h1 : ∀ x ∈ F, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : ℂ_[l])‖)
    (h2 : ∀ x ∈ F, ‖x‖ ≤ 1 → ‖x ^ (l ^ N) - x‖ < 1) :
    ∀ y ∈ F.topologicalClosure, ‖y‖ ≤ 1 → ‖y ^ (l ^ N) - y‖ ≤ ‖(l : ℂ_[l])‖ := by
  intro y hy hy1
  obtain ⟨y', hy'F, hyy'⟩ := Metric.mem_closure_iff.1 hy _ (norm_l_pos (l := l))
  rw [dist_eq_norm] at hyy'
  have hl1 := (norm_l_lt_one (l := l)).le
  have hy'1 : ‖y'‖ ≤ 1 := by
    have : y' = y - (y - y') := by ring
    rw [this]
    exact (norm_sub_le_max _ _).trans (max_le hy1 (hyy'.le.trans hl1))
  have hF : ‖y' ^ (l ^ N) - y'‖ ≤ ‖(l : ℂ_[l])‖ :=
    h1 _ (F.sub_mem (F.pow_mem hy'F _) hy'F) (h2 y' hy'F hy'1)
  have hP : ‖y ^ (l ^ N) - y' ^ (l ^ N)‖ ≤ ‖(l : ℂ_[l])‖ :=
    (norm_pow_sub_pow_le hy1 hy'1 _).trans hyy'.le
  have : y ^ (l ^ N) - y = (y ^ (l ^ N) - y' ^ (l ^ N)) + ((y' ^ (l ^ N) - y') - (y - y')) := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hP
    ((norm_sub_le_max _ _).trans (max_le hF hyy'.le)))

theorem teich (hN : 0 < N) (G : Subfield ℂ_[l]) (hGc : IsClosed (G : Set ℂ_[l]))
    (hG : ∀ y ∈ G, ‖y‖ ≤ 1 → ‖y ^ (l ^ N) - y‖ ≤ ‖(l : ℂ_[l])‖) {x : ℂ_[l]} (hx : x ∈ G) (hx1 : ‖x‖ ≤ 1) :
    ∃ t ∈ G, t ∈ MaximalUnramifiedExtension l ∧ ‖x - t‖ ≤ ‖(l : ℂ_[l])‖ := by
  set q := l ^ N
  set L := ‖(l : ℂ_[l])‖ with hL
  have hl1 : L < 1 := norm_l_lt_one
  have hl0 : 0 < L := norm_l_pos
  let y : ℕ → ℂ_[l] := fun n => x ^ (q ^ n)
  have hys : ∀ n, y (n + 1) = y n ^ q := fun n => by
    simp only [y, pow_succ, pow_mul]
  have hy1 : ∀ n, ‖y n‖ ≤ 1 := fun n => by
    simp only [y, norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx1
  have hyG : ∀ n, y n ∈ G := fun n => G.pow_mem hx _
  have hLN : L ^ N ≤ L := pow_le_of_le_one hl0.le hl1.le hN.ne'
  have hstep : ∀ n, ‖y (n + 1) - y n‖ ≤ L * L ^ n := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, mul_one, hys]
      simpa [y] using hG x hx hx1
    | succ n ih =>
      have hd : ‖y (n + 1) - y n‖ ≤ L := ih.trans (mul_le_of_le_one_right hl0.le (pow_le_one₀ hl0.le hl1.le))
      rw [hys (n + 1), hys n]
      calc _ ≤ L ^ N * ‖y (n + 1) - y n‖ :=
            norm_pow_l_pow_sub_le l hl1.le (hy1 _) (hy1 _) (hys n ▸ hd) N |>.trans_eq' (by rw [hys n])
        _ ≤ L * (L * L ^ n) := by gcongr
        _ = L * L ^ (n + 1) := by ring
  have hcau : CauchySeq y := by
    refine cauchySeq_of_le_geometric L L hl1 fun n => ?_
    rw [dist_eq_norm, norm_sub_rev]
    exact hstep n
  obtain ⟨t, ht⟩ := cauchySeq_tendsto_of_complete hcau
  have htG : t ∈ G := hGc.mem_of_tendsto ht (Eventually.of_forall hyG)
  have htq : t ^ q = t := by
    have hA : Tendsto (fun n => y (n + 1)) atTop (𝓝 t) := (tendsto_add_atTop_iff_nat 1).2 ht
    have hB : Tendsto (fun n => y (n + 1)) atTop (𝓝 (t ^ q)) := by
      simp only [hys]
      exact ht.pow q
    exact tendsto_nhds_unique hB hA
  have hball : ∀ n, y n ∈ Metric.closedBall x L := by
    intro n
    rw [Metric.mem_closedBall, dist_eq_norm]
    induction n with
    | zero => simp [y, hl0.le]
    | succ n ih =>
      have : y (n + 1) - x = (y (n + 1) - y n) + (y n - x) := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((hstep n).trans (mul_le_of_le_one_right hl0.le (pow_le_one₀ hl0.le hl1.le))) ih)
  have htb := Metric.isClosed_closedBall.mem_of_tendsto ht (Eventually.of_forall hball)
  rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at htb
  exact ⟨t, htG, mem_Kur_of_pow_eq hN htq, htb⟩

end Padic

section Main

variable {l : ℕ} [Fact l.Prime]

theorem approx {N : ℕ} (hN : 0 < N) (G : Subfield ℂ_[l]) (hGc : IsClosed (G : Set ℂ_[l]))
    (hG : ∀ y ∈ G, ‖y‖ ≤ 1 → ‖y ^ (l ^ N) - y‖ ≤ ‖(l : ℂ_[l])‖) (k : ℕ) :
    ∀ x ∈ G, ‖x‖ ≤ 1 → ∃ s ∈ MaximalUnramifiedExtension l, ‖x - s‖ ≤ ‖(l : ℂ_[l])‖ ^ k := by
  induction k with
  | zero => exact fun x _ hx1 => ⟨0, (MaximalUnramifiedExtension l).zero_mem, by simpa using hx1⟩
  | succ k ih =>
    intro x hx hx1
    obtain ⟨t, htG, htK, hxt⟩ := teich N hN G hGc hG hx hx1
    have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_l_pos
    have hl0' : (l : ℂ_[l]) ≠ 0 := norm_pos_iff.1 hl0
    set x₁ := (x - t) / (l : ℂ_[l])
    have hx₁G : x₁ ∈ G := G.div_mem (G.sub_mem hx htG) (natCast_mem G l)
    have hx₁1 : ‖x₁‖ ≤ 1 := by
      rw [norm_div]; exact (div_le_one hl0).2 hxt
    obtain ⟨s₁, hs₁K, hs₁⟩ := ih x₁ hx₁G hx₁1
    refine ⟨t + (l : ℂ_[l]) * s₁, (MaximalUnramifiedExtension l).add_mem htK ((MaximalUnramifiedExtension l).mul_mem (natCast_mem (MaximalUnramifiedExtension l) l) hs₁K), ?_⟩
    have : x - (t + (l : ℂ_[l]) * s₁) = (l : ℂ_[l]) * (x₁ - s₁) := by
      simp only [x₁]; field_simp; ring
    rw [this, norm_mul, pow_succ']
    gcongr

end Main

open GlobalTheory.SubKur in

theorem le_Kur : ∀ (l : ℕ) [Fact l.Prime] (F : Subfield ℂ_[l]) (N : ℕ), 0 < N → (∀ x ∈ F, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : ℂ_[l])‖) →
    (∀ x ∈ F, ‖x‖ ≤ 1 → ‖x ^ (l ^ N) - x‖ < 1) → F ≤ MaximalUnramifiedExtension l := by
  intro l _ F N hN h1 h2
  have hG := closure_res F N h1 h2
  have hGc := F.isClosed_topologicalClosure
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := norm_l_lt_one
  have hKc : IsClosed (MaximalUnramifiedExtension l : Set ℂ_[l]) := Subfield.isClosed_topologicalClosure _
  have hint : ∀ x ∈ F, ‖x‖ ≤ 1 → x ∈ MaximalUnramifiedExtension l := by
    intro x hx hx1
    have hxG : x ∈ F.topologicalClosure := F.le_topologicalClosure hx
    rw [← SetLike.mem_coe, ← hKc.closure_eq]
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hl1
    obtain ⟨s, hsK, hs⟩ := approx hN _ hGc hG k x hxG hx1
    exact ⟨s, hsK, by rw [dist_eq_norm]; exact hs.trans_lt hk⟩
  intro x hx
  by_cases hx1 : ‖x‖ ≤ 1
  · exact hint x hx hx1
  · have hx0 : x ≠ 0 := by rintro rfl; simp at hx1
    have hi : ‖x⁻¹‖ ≤ 1 := by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hx1))
    have := (MaximalUnramifiedExtension l).inv_mem (hint x⁻¹ (F.inv_mem hx) hi)
    rwa [inv_inv] at this

end GlobalTheory.SubKur
