import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTeichDef

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKeyTeich

open RowTiePKey RowTiePE0

section Lim

variable {C : Type} [Field C] {V : VF C} {n : ℕ}

private theorem exists_ge_character_germs (x : C) : ∃ B : ℝ, V.Ge B x := by
  by_cases h : V.v x = ⊤
  · exact ⟨0, show ((0 : ℝ) : WithTop ℝ) ≤ V.v x by rw [h]; exact le_top⟩
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 h
    exact ⟨r, show ((r : ℝ) : WithTop ℝ) ≤ V.v x from le_of_eq hr⟩

private theorem tends_mul' {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun k => s k * t k) (x * y) := by
  obtain ⟨Bx, hBx⟩ := exists_ge_character_germs (V := V) x
  obtain ⟨By, hBy⟩ := exists_ge_character_germs (V := V) y
  unfold Tends at hs ht ⊢
  intro w
  obtain ⟨n1, hn1⟩ := ht By
  obtain ⟨n2, hn2⟩ := ht (w - Bx)
  obtain ⟨n3, hn3⟩ := hs (w - By)
  refine ⟨max n1 (max n2 n3), fun k hk => ?_⟩
  have h1 : n1 ≤ k := le_trans (le_max_left _ _) hk
  have h2 : n2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have h3 : n3 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have ht' : V.Ge By (t k) := by
    have e : t k = y + -(y - t k) := by ring
    rw [e]
    exact hBy.add (hn1 k h1).neg
  show V.Ge w (x * y - s k * t k)
  have e : x * y - s k * t k = x * (y - t k) + (x - s k) * t k := by ring
  rw [e]
  exact VF.Ge.add ((hBx.mul (hn2 k h2)).mono (by linarith)) (((hn3 k h3).mul ht').mono (by linarith))

private theorem tends_finset_sum {ι : Type} (S : Finset ι) {f : ι → ℕ → C} {g : ι → C}
    (h : ∀ i ∈ S, Tends V (f i) (g i)) : Tends V (fun k => ∑ i ∈ S, f i k) (∑ i ∈ S, g i) := by
  unfold Tends at h ⊢
  intro w
  choose! n0 hn0 using fun i hi => h i hi w
  refine ⟨S.sup n0, fun k hk => ?_⟩
  show V.Ge w (∑ i ∈ S, g i - ∑ i ∈ S, f i k)
  rw [← Finset.sum_sub_distrib]
  exact VF.Ge.sum fun i hi => hn0 i hi k (le_trans (Finset.le_sup hi) hk)

theorem tends_mul {s t : ℕ → Matrix (Fin n) (Fin n) C} {x y : Matrix (Fin n) (Fin n) C}
    (hs : ∀ i j, Tends V (fun k => s k i j) (x i j)) (ht : ∀ i j, Tends V (fun k => t k i j) (y i j)) (i j : Fin n) :
    Tends V (fun k => (s k * t k) i j) ((x * y) i j) := by
  simp only [Matrix.mul_apply]
  exact tends_finset_sum (f := fun m k => s k i m * t k m j) (g := fun m => x i m * y m j) Finset.univ
    (fun m _ => tends_mul' (hs i m) (ht m j))

theorem tends_pow {s : ℕ → Matrix (Fin n) (Fin n) C} {x : Matrix (Fin n) (Fin n) C}
    (hs : ∀ i j, Tends V (fun k => s k i j) (x i j)) (m : ℕ) (i j : Fin n) :
    Tends V (fun k => (s k ^ m) i j) ((x ^ m) i j) := by
  induction m generalizing i j with
  | zero =>
    simp only [pow_zero]
    unfold Tends
    intro w
    exact ⟨0, fun k _ => by simp only [sub_self]; exact VF.Ge.zero w⟩
  | succ m ih =>
    simp only [pow_succ]
    exact tends_mul (fun i j => ih i j) hs i j

theorem tends_shift {s : ℕ → C} {x : C} (h : Tends V s x) : Tends V (fun k => s (k + 1)) x := by
  unfold Tends at h ⊢
  intro w
  obtain ⟨n0, hn0⟩ := h w
  exact ⟨n0, fun k hk => hn0 (k + 1) (by omega)⟩

def IntM (V : VF C) (n : ℕ) : Subring (Matrix (Fin n) (Fin n) C) where
  carrier := {M | ∀ i j, V.Ge 0 (M i j)}
  mul_mem' := fun {a b} ha hb i j => by
    simp only [Matrix.mul_apply]
    exact VF.Ge.sum fun m _ => ((ha i m).mul (hb m j)).mono (by norm_num)
  one_mem' := fun i j => by
    by_cases h : i = j
    · simp only [Matrix.one_apply, h, if_true]; exact VF.Ge.one
    · simp only [Matrix.one_apply, h, if_false]; exact VF.Ge.zero 0
  add_mem' := fun {a b} ha hb i j => (ha i j).add (hb i j)
  zero_mem' := fun _ _ => VF.Ge.zero 0
  neg_mem' := fun {a} ha i j => (ha i j).neg

end Lim

private theorem l_cast_ne_zero {C : Type} [Field C] (V : VF C) : (V.l : C) ≠ 0 := by
  intro h0
  have h4 := V.4
  rw [h0, AddValuation.map_zero] at h4
  exact WithTop.top_ne_coe (h4.trans WithTop.coe_one.symm)

private theorem ge_one_l {C : Type} [Field C] (V : VF C) : V.Ge 1 (V.l : C) :=
  show ((1 : ℝ) : WithTop ℝ) ≤ V.v (V.l : C) from le_of_eq (by rw [V.4, WithTop.coe_one])

private theorem ge_zero_natCast {C : Type} [Field C] (V : VF C) (c : ℕ) : V.Ge 0 (c : C) := by
  induction c with
  | zero => rw [Nat.cast_zero]; exact VF.Ge.zero 0
  | succ c ih => rw [Nat.cast_succ]; exact ih.add VF.Ge.one

private theorem ge_one_natCast_of_l_dvd {C : Type} [Field C] {V : VF C} {c : ℕ} (h : V.l ∣ c) : V.Ge 1 (c : C) := by
  obtain ⟨m, rfl⟩ := h
  rw [Nat.cast_mul]
  exact ((ge_one_l V).mul (ge_zero_natCast V m)).mono (by norm_num)

private theorem ge_inv_l_mul_of_ge_add_one {C : Type} [Field C] {V : VF C} {w : ℝ} {e : C} (he : V.Ge (w + 1) e) :
    V.Ge w ((V.l : C)⁻¹ * e) := by
  have e1 : e = (V.l : C) * ((V.l : C)⁻¹ * e) := by
    rw [← mul_assoc, mul_inv_cancel₀ (l_cast_ne_zero V), one_mul]
  have h2 : ((w + 1 : ℝ) : WithTop ℝ) ≤ V.v (V.l : C) + V.v ((V.l : C)⁻¹ * e) := by
    rw [← AddValuation.map_mul, ← e1]
    exact he
  rw [V.4] at h2
  show ((w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C)⁻¹ * e)
  generalize V.v ((V.l : C)⁻¹ * e) = u at h2 ⊢
  induction u using WithTop.recTopCoe with
  | top => exact le_top
  | coe r =>
    rw [← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe] at h2
    rw [WithTop.coe_le_coe]
    linarith

private theorem eq_of_tends_of_tends {C : Type} [Field C] {V : VF C} {u : ℕ → C} {a c : C}
    (ha : Tends V u a) (hc : Tends V u c) : a = c := by
  by_contra hne
  have hne' : V.v (a - c) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact sub_ne_zero.2 hne
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne'
  unfold Tends at ha hc
  obtain ⟨n1, hn1⟩ := ha (r + 1)
  obtain ⟨n2, hn2⟩ := hc (r + 1)
  have h := (hn1 (max n1 n2) (le_max_left _ _)).add (hn2 (max n1 n2) (le_max_right _ _)).neg
  have e : a - u (max n1 n2) + -(c - u (max n1 n2)) = a - c := by ring
  rw [e] at h
  have h' : ((r + 1 : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ) := by
    rw [hr]
    exact h
  rw [WithTop.coe_le_coe] at h'
  linarith

private theorem ge_add_matrix_mul_entry_of_ge {C : Type} [Field C] {V : VF C} {n : ℕ} {P R : Matrix (Fin n) (Fin n) C}
    {a b : ℝ} (hP : ∀ i j, V.Ge a (P i j)) (hR : ∀ i j, V.Ge b (R i j)) :
    ∀ i j, V.Ge (a + b) ((P * R) i j) := by
  intro i j
  rw [Matrix.mul_apply]
  exact VF.Ge.sum fun m _ => (hP i m).mul (hR m j)

private theorem ge_zero_matrix_one_entry {C : Type} [Field C] (V : VF C) (n : ℕ) (i j : Fin n) :
    V.Ge 0 ((1 : Matrix (Fin n) (Fin n) C) i j) := by
  by_cases h : i = j
  · simp only [Matrix.one_apply, h, if_true]
    exact VF.Ge.one
  · simp only [Matrix.one_apply, h, if_false]
    exact VF.Ge.zero 0

private theorem ge_zero_matrix_pow_entry_of_ge_zero {C : Type} [Field C] {V : VF C} {n : ℕ} {P : Matrix (Fin n) (Fin n) C}
    (hP : ∀ i j, V.Ge 0 (P i j)) (m : ℕ) : ∀ i j, V.Ge 0 ((P ^ m) i j) := by
  induction m with
  | zero =>
    intro i j
    rw [pow_zero]
    exact ge_zero_matrix_one_entry V n i j
  | succ m ih =>
    intro i j
    rw [pow_succ]
    exact (ge_add_matrix_mul_entry_of_ge ih hP i j).mono (by norm_num)

private theorem ge_nsmul_matrix_pow_entry_of_ge {C : Type} [Field C] {V : VF C} {n : ℕ} {P : Matrix (Fin n) (Fin n) C}
    {t : ℝ} (hP : ∀ i j, V.Ge t (P i j)) (m : ℕ) : ∀ i j, V.Ge ((m : ℝ) * t) ((P ^ m) i j) := by
  induction m with
  | zero =>
    intro i j
    rw [pow_zero]
    exact (ge_zero_matrix_one_entry V n i j).mono (by simp)
  | succ m ih =>
    intro i j
    rw [pow_succ]
    exact (ge_add_matrix_mul_entry_of_ge ih hP i j).mono (le_of_eq (by push_cast; ring))

theorem teich_holds : TeichSt := by
  unfold TeichSt
  intro C _ V hcomp n d hd A hadd hneg hmul hcomm hint hclos hfrob b hb
  have h0 : (0 : Matrix (Fin n) (Fin n) C) ∈ A := by
    simpa using hadd b hb (-b) (hneg b hb)
  have hsub : ∀ a ∈ A, ∀ c ∈ A, a - c ∈ A := fun a ha c hc => by
    rw [sub_eq_add_neg]
    exact hadd a ha _ (hneg c hc)
  have hpow : ∀ a ∈ A, ∀ k : ℕ, a ^ (k + 1) ∈ A := by
    intro a ha k
    induction k with
    | zero =>
      rw [zero_add, pow_one]
      exact ha
    | succ k ih =>
      rw [pow_succ]
      exact hmul _ ih _ ha
  have hpowA : ∀ a ∈ A, ∀ k : ℕ, 0 < k → a ^ k ∈ A := by
    intro a ha k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hk)
    exact hpow a ha k'

  have Rl : ∀ x ∈ A, ∀ y ∈ A, ∀ t : ℝ, 1 ≤ t → (∀ i j, V.Ge t ((y - x) i j)) →
      ∀ i j, V.Ge (t + 1) ((y ^ V.l - x ^ V.l) i j) := by
    intro x hx y hy t ht hδ
    have hc : Commute x (y - x) := by
      show x * (y - x) = (y - x) * x
      rw [mul_sub, sub_mul, hcomm x hx y hy]
    have hexp : y ^ V.l - x ^ V.l = ∑ m ∈ Finset.range V.l,
        x ^ m * (y - x) ^ (V.l - m) * ((V.l.choose m : ℕ) : Matrix (Fin n) (Fin n) C) := by
      have e : x + (y - x) = y := by abel
      have h1 := hc.add_pow V.l
      rw [e, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
        mul_one] at h1
      rw [h1]
      abel
    have hl2 : 2 ≤ V.l := V.3.two_le
    have ht0 : (0 : ℝ) ≤ t := by linarith
    intro i j
    rw [hexp, Matrix.sum_apply]
    refine VF.Ge.sum fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul]
    have hP := ge_add_matrix_mul_entry_of_ge (ge_zero_matrix_pow_entry_of_ge_zero (hint x hx) m) (ge_nsmul_matrix_pow_entry_of_ge hδ (V.l - m)) i j
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · have hL : (2 : ℝ) ≤ ((V.l - 0 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ V.l - 0)
      refine ((ge_zero_natCast V (V.l.choose 0)).mul hP).mono ?_
      nlinarith [mul_le_mul_of_nonneg_right hL ht0]
    · have hdiv : V.l ∣ V.l.choose m := V.3.dvd_choose_self (by omega) hm
      have hL : (1 : ℝ) ≤ ((V.l - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ V.l - m)
      refine ((ge_one_natCast_of_l_dvd hdiv).mul hP).mono ?_
      nlinarith [mul_le_mul_of_nonneg_right hL ht0]
  have Rd : ∀ e : ℕ, ∀ x ∈ A, ∀ y ∈ A, ∀ t : ℝ, 1 ≤ t → (∀ i j, V.Ge t ((y - x) i j)) →
      ∀ i j, V.Ge (t + e) ((y ^ V.l ^ e - x ^ V.l ^ e) i j) := by
    intro e
    induction e with
    | zero =>
      intro x hx y hy t ht h i j
      simp only [pow_zero, pow_one, Nat.cast_zero, add_zero]
      exact h i j
    | succ e ih =>
      intro x hx y hy t ht h i j
      have hpos : 0 < V.l ^ e := pow_pos V.3.pos e
      have h1 := ih x hx y hy t ht h
      have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      have h2 := Rl _ (hpowA x hx _ hpos) _ (hpowA y hy _ hpos) (t + e) (by linarith) h1 i j
      rw [pow_succ, pow_mul, pow_mul]
      exact h2.mono (le_of_eq (by push_cast; ring))

  obtain ⟨s, hs⟩ : ∃ s : ℕ → Matrix (Fin n) (Fin n) C, ∀ k, s k = b ^ ((V.l ^ d) ^ k) :=
    ⟨_, fun k => rfl⟩
  have hq : 0 < V.l ^ d := pow_pos V.3.pos d
  have hsA : ∀ k, s k ∈ A := fun k => by
    rw [hs]
    exact hpowA b hb _ (pow_pos hq k)
  have hsS : ∀ k, s (k + 1) = s k ^ V.l ^ d := fun k => by
    rw [hs, hs, pow_succ, pow_mul]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd
  have hD : ∀ k : ℕ, ∀ i j, V.Ge ((k : ℝ) + 1) ((s (k + 1) - s k) i j) := by
    intro k
    induction k with
    | zero =>
      intro i j
      rw [hsS 0]
      have hm := hint _ (hfrob (s 0) (hsA 0)) i j
      have e : s 0 ^ V.l ^ d - s 0 = (V.l : C) • ((V.l : C)⁻¹ • (s 0 ^ V.l ^ d - s 0)) := by
        rw [smul_smul, mul_inv_cancel₀ (l_cast_ne_zero V), one_smul]
      rw [e, Matrix.smul_apply, smul_eq_mul]
      exact ((ge_one_l V).mul hm).mono (by norm_num)
    | succ k ih =>
      intro i j
      have e : s (k + 1 + 1) - s (k + 1) = s (k + 1) ^ V.l ^ d - s k ^ V.l ^ d := by
        rw [← hsS, ← hsS]
      rw [e]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      exact (Rd d _ (hsA k) _ (hsA (k + 1)) ((k : ℝ) + 1) (by linarith) ih i j).mono
        (by push_cast; linarith)
  have hcau : ∀ i j, ∃ x : C, ∀ k : ℕ, V.Ge (k : ℝ) (x - s k i j) := fun i j =>
    hcomp (fun k => s k i j) (fun k => (hD k i j).mono (by linarith))
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) C, ∀ i j (k : ℕ), V.Ge (k : ℝ) (T i j - s k i j) :=
    ⟨Matrix.of fun i j => Classical.choose (hcau i j), fun i j k => Classical.choose_spec (hcau i j) k⟩
  have hTt : ∀ i j, Tends V (fun k => s k i j) (T i j) := by
    intro i j
    unfold Tends
    intro w
    exact ⟨⌈w⌉₊, fun k hk => (hT i j k).mono (le_trans (Nat.le_ceil w) (by exact_mod_cast hk))⟩
  have hTA : T ∈ A := hclos s T hsA hTt
  have hTq : T ^ V.l ^ d = T := by
    ext i j
    have h1 := tends_pow hTt (V.l ^ d) i j
    simp only [← hsS] at h1
    exact eq_of_tends_of_tends h1 (tends_shift (hTt i j))
  have hbs : ∀ k, (V.l : C)⁻¹ • (b - s k) ∈ A := by
    intro k
    induction k with
    | zero =>
      rw [hs 0, pow_zero, pow_one, sub_self, smul_zero]
      exact h0
    | succ k ih =>
      have e : (V.l : C)⁻¹ • (b - s (k + 1)) =
          (V.l : C)⁻¹ • (b - s k) - (V.l : C)⁻¹ • (s k ^ V.l ^ d - s k) := by
        rw [hsS k, ← smul_sub]
        congr 1
        abel
      rw [e]
      exact hsub _ ih _ (hfrob _ (hsA k))
  have hlim : ∀ i j, Tends V (fun k => ((V.l : C)⁻¹ • (b - s k)) i j) (((V.l : C)⁻¹ • (b - T)) i j) := by
    intro i j
    have h1 := hTt i j
    unfold Tends at h1 ⊢
    intro w
    obtain ⟨n0, hn0⟩ := h1 (w + 1)
    refine ⟨n0, fun k hk => ?_⟩
    show V.Ge w (((V.l : C)⁻¹ • (b - T)) i j - ((V.l : C)⁻¹ • (b - s k)) i j)
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    have e : (V.l : C)⁻¹ * (b i j - T i j) - (V.l : C)⁻¹ * (b i j - s k i j) =
        (V.l : C)⁻¹ * -(T i j - s k i j) := by ring
    rw [e]
    exact ge_inv_l_mul_of_ge_add_one (hn0 k hk).neg
  exact ⟨T, hTA, hTq, hclos _ _ hbs hlim⟩

end RowTiePKeyTeich

end Formalism.L2.FormalSeriesBounds
