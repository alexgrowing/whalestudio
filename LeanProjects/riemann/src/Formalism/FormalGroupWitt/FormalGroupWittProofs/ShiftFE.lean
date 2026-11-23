import Formalism.FormalGroupWitt.Statement

noncomputable section

universe u

namespace Formalism.FG
namespace ShiftFEAux

open MvPowerSeries

variable {K : Type*} [Field K] {l m : ℕ}

lemma pow_inj (hl : 2 ≤ l) {a b : ℕ} (h : (l ^ 2) ^ a = (l ^ 2) ^ b) : a = b :=
  Nat.pow_right_injective (le_trans hl (Nat.le_self_pow two_ne_zero l)) h

lemma eq_zero_of_pow_eq_one (hl : 2 ≤ l) {a : ℕ} (h : (l ^ 2) ^ a = 1) : a = 0 :=
  pow_inj hl (h.trans (pow_zero _).symm)

lemma coeff_shiftLog (j : ZMod m) (n : ZMod m →₀ ℕ) :
    coeff n (shiftLog K l m j) = ∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by
  rw [coeff_apply]; rfl

lemma coeff_shiftLog_single (hl : 2 ≤ l) (j : ZMod m) (e : ℕ) :
    coeff (Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)) (shiftLog K l m j) =
      ((l : K) ^ e)⁻¹ := by
  rw [coeff_shiftLog, Finsupp.degree_single]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    have := congrArg Finsupp.degree h
    simp only [Finsupp.degree_single] at this
    exact hb (pow_inj hl this).symm
  · intro he
    exfalso; apply he
    rw [Finset.mem_range]
    have : e < (l ^ 2) ^ e := Nat.lt_pow_self (by nlinarith)
    omega

lemma coeff_shiftLog_zero (j : ZMod m) (n : ZMod m →₀ ℕ)
    (h : ∀ e : ℕ, n ≠ Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)) :
    coeff n (shiftLog K l m j) = 0 := by
  rw [coeff_shiftLog]
  exact Finset.sum_eq_zero fun e _ => if_neg (h e)

lemma map_shiftLog (σ : K →+* K) (k : ZMod m) :
    map σ (shiftLog K l m k) = shiftLog K l m k := by
  ext n
  rw [coeff_map, coeff_shiftLog, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp [map_inv₀]

lemma idMod2 (hl : 2 ≤ l) : IsIdMod2 (shiftLog K l m) := by
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    apply coeff_shiftLog_zero
    intro e h
    have := congrArg Finsupp.degree h
    simp only [Finsupp.degree_single] at this
    have hpos : 0 < (l ^ 2) ^ e := by positivity
    have h0 : (0 : ZMod m →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
    omega
  · by_cases hij : i = j
    · subst hij
      have := coeff_shiftLog_single (K := K) hl i 0
      simpa using this
    · rw [if_neg hij]
      apply coeff_shiftLog_zero
      intro e h
      have hd := congrArg Finsupp.degree h
      simp only [Finsupp.degree_single] at hd
      have he := eq_zero_of_pow_eq_one hl hd.symm
      subst he
      apply hij
      simpa using (Finsupp.single_left_inj one_ne_zero).mp h

lemma main [CharZero K] (hl : l.Prime) [NeZero m] (σ : K →+* K) (j : ZMod m) :
    shiftLog K l m j - (l : K)⁻¹ • ∑ k, shiftMat K m j k •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLog K l m k)) = MvPowerSeries.X j := by
  have hl2 : 2 ≤ l := hl.two_le
  have hsum : ∑ k, shiftMat K m j k •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLog K l m k)) =
      MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero) (shiftLog K l m (j - 1)) := by
    simp [shiftMat, map_shiftLog]
  rw [hsum]
  ext n
  simp only [map_sub, map_smul, smul_eq_mul, coeff_X]
  by_cases hA : ∃ e : ℕ, n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)
  · obtain ⟨e, rfl⟩ := hA
    rw [coeff_shiftLog_single hl2]
    obtain _ | e := e
    · simp only [Nat.cast_zero, sub_zero, pow_zero, inv_one, if_true]
      rw [coeff_expand_of_not_dvd (i := j)]
      · ring
      · rw [Finsupp.single_eq_same, Nat.dvd_one]
        intro h
        nlinarith
    · have hne : Finsupp.single (j - ((e + 1 : ℕ) : ZMod m)) ((l ^ 2) ^ (e + 1)) ≠
          Finsupp.single j 1 := by
        intro h
        have hd := congrArg Finsupp.degree h
        simp only [Finsupp.degree_single] at hd
        exact absurd (eq_zero_of_pow_eq_one hl2 hd) (Nat.succ_ne_zero e)
      rw [if_neg hne]
      have hn : Finsupp.single (j - ((e + 1 : ℕ) : ZMod m)) ((l ^ 2) ^ (e + 1)) =
          (l ^ 2) • Finsupp.single ((j - 1) - (e : ZMod m)) ((l ^ 2) ^ e) := by
        rw [Finsupp.smul_single, smul_eq_mul, ← pow_succ']
        congr 1
        push_cast
        ring
      rw [hn, coeff_expand_smul, coeff_shiftLog_single hl2]
      ring
  · push Not at hA
    rw [coeff_shiftLog_zero j n hA, if_neg (by simpa using hA 0)]
    suffices h : coeff n (MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
        (shiftLog K l m (j - 1))) = 0 by rw [h]; ring
    by_cases hd : ∀ i, l ^ 2 ∣ n i
    · have hn : n = (l ^ 2) • Finsupp.mapRange (fun x => x / l ^ 2) (Nat.zero_div _) n := by
        ext i
        simp [Nat.mul_div_cancel' (hd i)]
      rw [hn, coeff_expand_smul]
      apply coeff_shiftLog_zero
      intro e he
      apply hA (e + 1)
      rw [hn, he, Finsupp.smul_single, smul_eq_mul, ← pow_succ']
      congr 1
      push_cast
      ring
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      exact coeff_expand_of_not_dvd _ _ _ hi

end ShiftFEAux

open ShiftFEAux in
theorem shift_functional_equation : Formalism.FG.ShiftFunEq.{u} := by
  intro K _ _ l hl m _ σ
  exact ⟨idMod2 hl.two_le, fun j => main hl σ j⟩

end Formalism.FG
