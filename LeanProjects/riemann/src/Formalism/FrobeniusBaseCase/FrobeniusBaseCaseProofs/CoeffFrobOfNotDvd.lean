import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.IdentityTwentyB

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}

theorem le_add_coe_iff (x : WithTop ℝ) (w c : ℝ) :
    (w : WithTop ℝ) ≤ x + (c : WithTop ℝ) ↔ ((w - c : ℝ) : WithTop ℝ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe y => rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]

theorem hasWt_iff : HasWt v r w f ↔
    ∀ A : Z →₀ ℕ, ((w - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) ≤ v (coeff A f) := by
  unfold HasWt
  exact forall_congr' fun A => le_add_coe_iff _ _ _

theorem HasWt.mono (h : w' ≤ w) (hf : HasWt v r w f) : HasWt v r w' f := by
  rw [hasWt_iff] at *
  intro A
  refine le_trans ?_ (hf A)
  exact WithTop.coe_le_coe.2 (by linarith)

theorem HasWt.zero : HasWt v r w (0 : MvPowerSeries Z k) := by
  rw [hasWt_iff]; intro A; simp

theorem HasWt.add (hf : HasWt v r w f) (hg : HasWt v r w g) : HasWt v r w (f + g) := by
  rw [hasWt_iff] at *
  intro A
  rw [map_add]
  exact le_trans (le_min (hf A) (hg A)) (v.map_add _ _)

theorem HasWt.neg (hf : HasWt v r w f) : HasWt v r w (-f) := by
  rw [hasWt_iff] at *
  intro A
  rw [map_neg, v.map_neg]
  exact hf A

theorem HasWt.sub (hf : HasWt v r w f) (hg : HasWt v r w g) : HasWt v r w (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem HasWt.sum {ι : Type*} (s : Finset ι) {F : ι → MvPowerSeries Z k}
    (h : ∀ i ∈ s, HasWt v r w (F i)) : HasWt v r w (∑ i ∈ s, F i) := by
  rw [hasWt_iff]
  intro A
  rw [map_sum]
  exact v.map_le_sum fun i hi => (hasWt_iff.1 (h i hi)) A

theorem HasWt.mul (hf : HasWt v r w1 f) (hg : HasWt v r w2 g) : HasWt v r (w1 + w2) (f * g) := by
  classical
  rw [hasWt_iff] at *
  intro A
  rw [coeff_mul]
  refine v.map_le_sum fun p hp => ?_
  rw [v.map_mul]
  have hA : A = p.1 + p.2 := (Finset.HasAntidiagonal.mem_antidiagonal.1 hp).symm
  have hd : ((A.degree : ℕ) : ℝ) = ((p.1.degree : ℕ) : ℝ) + ((p.2.degree : ℕ) : ℝ) := by
    rw [hA, map_add]; push_cast; ring
  have : ((w1 + w2 - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ)
      = ((w1 - ((p.1.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ)
        + ((w2 - ((p.2.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add, hd]; congr 1; ring
  rw [this]
  exact add_le_add (hf p.1) (hg p.2)

theorem HasWt.C_mul {x : k} (hx : ((a₀ : ℝ) : WithTop ℝ) ≤ v x) (hf : HasWt v r w f) :
    HasWt v r (a₀ + w) (C x * f) := by
  rw [hasWt_iff] at *
  intro A
  rw [coeff_C_mul, v.map_mul]
  have : ((a₀ + w - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ)
      = ((a₀ : ℝ) : WithTop ℝ) + ((w - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add]; congr 1; ring
  rw [this]
  exact add_le_add hx (hf A)

theorem HasWt.mul_C {x : k} (hx : ((a₀ : ℝ) : WithTop ℝ) ≤ v x) (hf : HasWt v r w f) :
    HasWt v r (a₀ + w) (f * C x) := by
  rw [mul_comm]; exact hf.C_mul hx

theorem HasWt.one : HasWt v r 0 (1 : MvPowerSeries Z k) := by
  classical
  rw [hasWt_iff]
  intro A
  rw [coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

theorem HasWt.pow (hf : HasWt v r w f) (n : ℕ) : HasWt v r ((n : ℝ) * w) (f ^ n) := by
  induction n with
  | zero => simpa using (HasWt.one : HasWt v r 0 (1 : MvPowerSeries Z k))
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hf
    convert this using 1
    push_cast; ring

theorem HasWt.X (d : Z) : HasWt v r r (X d : MvPowerSeries Z k) := by
  classical
  rw [hasWt_iff]
  intro A
  rw [coeff_X]
  split_ifs with h
  · subst h; simp
  · simp

theorem coeff_frob_of_dvd {N : ℕ} {B : Z →₀ ℕ} (h : ∀ d, N ∣ B d) (f : MvPowerSeries Z k) :
    coeff B (frob N f) = (coeff (B.mapRange (· / N) (Nat.zero_div N)) f) ^ N := by
  show frob N f B = _
  unfold frob
  rw [if_pos h]

theorem coeff_frob_of_not_dvd {N : ℕ} {B : Z →₀ ℕ} (h : ¬ ∀ d, N ∣ B d) (f : MvPowerSeries Z k) :
    coeff B (frob N f) = 0 := by
  show frob N f B = _
  unfold frob
  rw [if_neg h]

theorem smul_mapRange_div {N : ℕ} {B : Z →₀ ℕ} (h : ∀ d, N ∣ B d) :
    N • (B.mapRange (· / N) (Nat.zero_div N)) = B := by
  ext d
  simp only [Finsupp.coe_smul, Pi.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact Nat.mul_div_cancel' (h d)

theorem HasWt.frob (hf : HasWt v r w f) (N : ℕ) : HasWt v r ((N : ℝ) * w) (frob N f) := by
  rw [hasWt_iff] at *
  intro B
  by_cases h : ∀ d, N ∣ B d
  · rw [coeff_frob_of_dvd h, v.map_pow]
    set B' := B.mapRange (· / N) (Nat.zero_div N) with hB'
    have hB : B = N • B' := (smul_mapRange_div h).symm
    have hd : ((B.degree : ℕ) : ℝ) = (N : ℝ) * ((B'.degree : ℕ) : ℝ) := by
      rw [hB, map_nsmul]; simp
    have h1 := nsmul_le_nsmul_right (hf B') N
    refine le_trans (le_of_eq ?_) h1
    rw [← WithTop.coe_nsmul, hd]
    congr 1
    rw [nsmul_eq_mul]; ring
  · rw [coeff_frob_of_not_dvd h]; simp

theorem frob_zero {N : ℕ} (hN : 1 ≤ N) : frob N (0 : MvPowerSeries Z k) = 0 := by
  ext B
  by_cases h : ∀ d, N ∣ B d
  · rw [coeff_frob_of_dvd h]; simp; omega
  · rw [coeff_frob_of_not_dvd h]; simp

theorem v_natCast_nonneg (v : AddValuation k (WithTop ℝ)) (n : ℕ) : 0 ≤ v (n : k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    refine le_trans (le_min ih ?_) (v.map_add _ _)
    rw [v.map_one]

theorem HasWt.natCast_mul {l n : ℕ} (hv : v (l : k) = 1) (hd : l ∣ n) (hf : HasWt v r w f) :
    HasWt v r (1 + w) ((n : MvPowerSeries Z k) * f) := by
  have h1 : (n : MvPowerSeries Z k) = C (n : k) := (map_natCast C n).symm
  rw [h1]
  refine hf.C_mul ?_
  obtain ⟨m, rfl⟩ := hd
  push_cast
  rw [v.map_mul, hv]
  have := v_natCast_nonneg v m
  calc (1 : WithTop ℝ) = 1 + 0 := by simp
    _ ≤ 1 + v (m : k) := by gcongr

theorem hasWt_add_pow_sub_pow {l q : ℕ} (hv : v (l : k) = 1) (hq : 1 ≤ q)
    (hdiv : ∀ m, 0 < m → m < q → l ∣ q.choose m) (hw : wa ≤ wb)
    (ha : HasWt v r wa a) (hb : HasWt v r wb b) :
    HasWt v r (1 + ((q : ℝ) - 1) * wa + wb) ((a + b) ^ q - a ^ q - b ^ q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have key : (a + b) ^ (p + 1) - a ^ (p + 1) - b ^ (p + 1)
      = ∑ m ∈ Finset.range p, ((p + 1).choose (m + 1) : MvPowerSeries Z k)
          * (a ^ (m + 1) * b ^ (p + 1 - (m + 1))) := by
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_zero,
      one_mul, Nat.choose_zero_right]
    rw [add_sub_cancel_right, add_sub_cancel_right]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [key]
  refine HasWt.sum _ fun m hm => ?_
  have hm' : m < p := Finset.mem_range.1 hm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hm'
  have h1 := ((ha.pow (m + 1)).mul (hb.pow (m + j + 1 + 1 - (m + 1)))).natCast_mul hv
    (hdiv (m + 1) (by omega) (by omega))
  refine h1.mono ?_
  have h2 : m + j + 1 + 1 - (m + 1) = j + 1 := by omega
  rw [h2]
  push_cast
  have : 0 ≤ (j : ℝ) * (wb - wa) := mul_nonneg (Nat.cast_nonneg j) (by linarith)
  nlinarith

theorem hasWt_add_pow_sub {l e : ℕ} (hl : l.Prime) (hv : v (l : k) = 1) (hw : wa ≤ wb)
    (ha : HasWt v r wa a) (hb : HasWt v r wb b) :
    HasWt v r (1 + (((l ^ e : ℕ) : ℝ) - 1) * wa + wb)
      ((a + b) ^ (l ^ e) - a ^ (l ^ e) - b ^ (l ^ e)) :=
  hasWt_add_pow_sub_pow hv (Nat.one_le_pow _ _ hl.pos)
    (fun m h0 h1 => hl.dvd_choose_pow (by omega) (by omega)) hw ha hb

theorem hasWt_sum_pow_sub {ι : Type*} {l e : ℕ} (hl : l.Prime) (hv : v (l : k) = 1) (_he : 1 ≤ e)
    (s : Finset ι) {F : ι → MvPowerSeries Z k} (h : ∀ i ∈ s, HasWt v r w (F i)) :
    HasWt v r (1 + ((l ^ e : ℕ) : ℝ) * w) ((∑ i ∈ s, F i) ^ (l ^ e) - ∑ i ∈ s, (F i) ^ (l ^ e)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : l ^ e ≠ 0 := pow_ne_zero _ hl.ne_zero
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow this, sub_zero]
    exact HasWt.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h1 := hasWt_add_pow_sub (e := e) hl hv le_rfl (h i (Finset.mem_insert_self i s))
      (HasWt.sum s fun j hj => h j (Finset.mem_insert_of_mem hj))
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have h3 := (h1.mono (w' := 1 + ((l ^ e : ℕ) : ℝ) * w) (by linarith)).add h2
    convert h3 using 1
    ring

theorem coeff_sum_C_mul_X_pow [Fintype Z] [DecidableEq Z] (y : Z → k) (M : ℕ) (B : Z →₀ ℕ) :
    coeff B (∑ d, C (y d) * X d ^ M : MvPowerSeries Z k)
      = ∑ d, if B = Finsupp.single d M then y d else 0 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp

theorem frob_sum_X [Fintype Z] {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (x : Z → k) :
    frob N (∑ d, C (x d) * X d ^ M) = ∑ d, C (x d ^ N) * X d ^ (N * M) := by
  classical
  ext B
  rw [coeff_sum_C_mul_X_pow]
  by_cases hB : ∃ d0, B = Finsupp.single d0 (N * M)
  · obtain ⟨d0, rfl⟩ := hB
    have h1 : ∀ d, N ∣ (Finsupp.single d0 (N * M)) d := by
      intro d
      by_cases h : d0 = d
      · subst h; simp
      · simp [h]
    have h2 : (Finsupp.single d0 (N * M)).mapRange (· / N) (Nat.zero_div N)
        = Finsupp.single d0 M := by
      rw [Finsupp.mapRange_single]
      congr 1
      exact Nat.mul_div_cancel_left M (by omega)
    rw [coeff_frob_of_dvd h1, h2, coeff_sum_C_mul_X_pow]
    have hNM : N * M ≠ 0 := by positivity
    have hM0 : M ≠ 0 := by omega
    simp only [Finsupp.single_left_inj hNM, Finsupp.single_left_inj hM0]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp
  · have hR : ∀ d, B ≠ Finsupp.single d (N * M) := fun d h => hB ⟨d, h⟩
    rw [Finset.sum_eq_zero (fun d _ => if_neg (hR d))]
    by_cases h : ∀ d, N ∣ B d
    · rw [coeff_frob_of_dvd h, coeff_sum_C_mul_X_pow]
      have hL : ∀ d, B.mapRange (· / N) (Nat.zero_div N) ≠ Finsupp.single d M := by
        intro d hd
        apply hR d
        rw [← smul_mapRange_div h, hd, Finsupp.smul_single, smul_eq_mul]
      rw [Finset.sum_eq_zero (fun d _ => if_neg (hL d))]
      exact zero_pow (by omega)
    · rw [coeff_frob_of_not_dvd h]

end Formalism.BaseCaseIdentities
