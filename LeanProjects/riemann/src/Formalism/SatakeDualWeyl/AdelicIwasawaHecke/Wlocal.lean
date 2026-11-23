import Formalism.SatakeDualWeyl.StatementW
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

open MvPolynomial

noncomputable section

namespace Formalism.UG.P

open Formalism.GradedWeylDivisibility

def wlocal_E {R : Type} [CommRing R] {r : ℕ} (a b : Fin r) (c : R) : Matrix (Fin r) (Fin r) R :=
  fun i j => (if i = j then 1 else 0) + (if i = a ∧ j = b then c else 0)

def wlocal_L {R : Type} [CommRing R] {r : ℕ} (k : Fin r) (c : Fin r → R) : Matrix (Fin r) (Fin r) R :=
  fun i j => (if i = j then 1 else 0) + (if i ≠ k ∧ j = k then c i else 0)

section

variable {R : Type} [CommRing R]

lemma wlocal_E_mul_apply {r : ℕ} (a b : Fin r) (c : R) (M : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    (wlocal_E a b c * M) i j = M i j + (if i = a then c * M b j else 0) := by
  by_cases h : i = a <;> simp [Matrix.mul_apply, wlocal_E, add_mul, Finset.sum_add_distrib, h]

lemma wlocal_L_mul_apply {r : ℕ} (k : Fin r) (c : Fin r → R) (M : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    (wlocal_L k c * M) i j = M i j + (if i ≠ k then c i * M k j else 0) := by
  by_cases h : i = k <;> simp [Matrix.mul_apply, wlocal_L, add_mul, Finset.sum_add_distrib, h]

lemma wlocal_rowAct_mul {r n : ℕ} (A B : Matrix (Fin r) (Fin r) R) :
    rowAct R (n := n) (A * B) = (rowAct R B).comp (rowAct R A) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

lemma wlocal_rowAct_one {r n : ℕ} : rowAct R (n := n) (1 : Matrix (Fin r) (Fin r) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1]
  · simp [Matrix.one_apply_eq]
  · intro b _ hb
    simp [Matrix.one_apply_ne (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma C_ite_add_ite_mul {σ : Type} (p q : Prop) [Decidable p] [Decidable q] (c : R)
    (Y : MvPolynomial σ R) :
    C ((if p then 1 else 0) + (if q then c else 0)) * Y = (if p then Y else 0) + (if q then C c * Y else 0) := by
  split_ifs <;> simp [add_mul]

lemma wlocal_eval_rowGen {r n : ℕ} (a b : Fin r) (c : R) (f : MvPolynomial (Fin r × Fin n) R) :
    Polynomial.eval (C c) (rowGen R b a f) = rowAct R (wlocal_E a b c) f := by
  refine MvPolynomial.induction_on
    (motive := fun f => Polynomial.eval (C c) (rowGen R b a f) = rowAct R (wlocal_E a b c) f) f ?_ ?_ ?_
  · intro x
    simp [rowGen, rowAct, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  · intro p q hp hq
    rw [map_add, map_add, Polynomial.eval_add, hp, hq]
  · intro p v hp
    rw [map_mul, map_mul, Polynomial.eval_mul, hp]
    congr 1
    obtain ⟨i, j⟩ := v
    simp only [rowGen, rowAct, aeval_X, wlocal_E, C_ite_add_ite_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Polynomial.eval_add, Polynomial.eval_C]
    by_cases h : i = a
    · simp [h] <;> ring
    · simp [h]

def wlocal_Good {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (M : Matrix (Fin r) (Fin r) R) : Prop :=
  ∀ f ∈ weyl R r n hn ν, rowAct R M f ∈ weyl R r n hn ν

lemma wlocal_good_one {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    wlocal_Good hn ν (1 : Matrix (Fin r) (Fin r) R) := by
  intro f hf
  rw [wlocal_rowAct_one]
  exact hf

lemma wlocal_good_mul {r n : ℕ} {hn : n ≤ r} {ν : Fin n → ℕ} {A B : Matrix (Fin r) (Fin r) R}
    (hA : wlocal_Good hn ν A) (hB : wlocal_Good hn ν B) : wlocal_Good hn ν (A * B) := by
  intro f hf
  rw [wlocal_rowAct_mul, AlgHom.comp_apply]
  exact hB _ (hA f hf)

private lemma coeff_rowGen_mem_weyl {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) :
    (rowGen R a b f).coeff k ∈ weyl R r n hn ν := by
  unfold weyl at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro x hx
    obtain ⟨w, rfl⟩ := hx
    unfold weyl
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [map_add, Polynomial.coeff_add]
    exact Submodule.add_mem _ hx hy
  · intro m x _ hx
    rw [map_smul, Polynomial.coeff_smul]
    exact Submodule.smul_mem _ m hx

lemma wlocal_good_E {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (c : R) :
    wlocal_Good hn ν (wlocal_E a b c) := by
  intro f hf
  rw [← wlocal_eval_rowGen, Polynomial.eval_eq_sum_range]
  apply Submodule.sum_mem
  intro k _
  rw [← map_pow, mul_comm, ← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (coeff_rowGen_mem_weyl hn ν b a k f hf)

end

section

variable {R : Type} [CommRing R]

lemma wlocal_E_zero {r : ℕ} (a b : Fin r) : wlocal_E a b (0 : R) = 1 := by
  ext i j
  simp [wlocal_E, Matrix.one_apply]

lemma wlocal_E_mul_E {r : ℕ} (a b : Fin r) (c d : R) :
    wlocal_E a b c * wlocal_E a b d = wlocal_E a b (c + d + (if a = b then c * d else 0)) := by
  ext i j
  rw [wlocal_E_mul_apply]
  simp only [wlocal_E]
  by_cases hi : i = a
  · rw [hi]
    by_cases hj : j = b
    · rw [hj]
      by_cases hab : a = b
      · rw [hab]
        simp <;> ring
      · simp [hab, Ne.symm hab] <;> ring
    · simp [hj, Ne.symm hj]
  · simp [hi]

lemma wlocal_L_mul_L {r : ℕ} (k : Fin r) (c d : Fin r → R) :
    wlocal_L k c * wlocal_L k d = wlocal_L k (c + d) := by
  ext i j
  rw [wlocal_L_mul_apply]
  simp only [wlocal_L, Pi.add_apply]
  by_cases hi : i = k
  · rw [hi]
    simp
  · by_cases hj : j = k
    · rw [hj]
      simp [hi] <;> ring
    · simp [hi, hj, Ne.symm hj]

lemma wlocal_L_one {r : ℕ} (k : Fin r) : wlocal_L k (0 : Fin r → R) = 1 := by
  ext i j
  simp [wlocal_L, Matrix.one_apply]

lemma wlocal_L_congr {r : ℕ} (k : Fin r) (c d : Fin r → R) (h : ∀ i, i ≠ k → c i = d i) :
    wlocal_L k c = wlocal_L k d := by
  ext i j
  simp only [wlocal_L]
  by_cases hi : i = k
  · simp [hi]
  · rw [h i hi]

lemma wlocal_L_insert {r : ℕ} (k a : Fin r) (c : Fin r → R) (s : Finset (Fin r)) (ha : a ∉ s) (hak : a ≠ k) :
    wlocal_L k (fun i => if i ∈ insert a s then c i else 0) =
      wlocal_E a k (c a) * wlocal_L k (fun i => if i ∈ s then c i else 0) := by
  ext i j
  rw [wlocal_E_mul_apply]
  simp only [wlocal_L, Finset.mem_insert]
  by_cases hi : i = a
  · rw [hi]
    by_cases hj : j = k
    · rw [hj]
      simp [hak, ha]
    · simp [hak, ha, hj, Ne.symm hj]
  · simp [hi]

lemma wlocal_good_L {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (k : Fin r) (c : Fin r → R) :
    wlocal_Good hn ν (wlocal_L k c) := by
  have key : ∀ s : Finset (Fin r), wlocal_Good hn ν (wlocal_L k (fun i => if i ∈ s then c i else 0)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [show (fun i : Fin r => if i ∈ (∅ : Finset (Fin r)) then c i else 0) = 0 from
        funext fun i => by simp, wlocal_L_one]
      exact wlocal_good_one hn ν
    · intro a s ha ih
      by_cases hak : a = k
      · rw [wlocal_L_congr k (fun i => if i ∈ insert a s then c i else 0) (fun i => if i ∈ s then c i else 0)
          (by
            intro i hi
            have hia : i ≠ a := fun h => hi (h.trans hak)
            simp [Finset.mem_insert, hia])]
        exact ih
      · rw [wlocal_L_insert k a c s ha hak]
        exact wlocal_good_mul (wlocal_good_E hn ν a k (c a)) ih
  have h := key Finset.univ
  rwa [show (fun i : Fin r => if i ∈ (Finset.univ : Finset (Fin r)) then c i else 0) = c from
    funext fun i => by simp] at h

end

section

variable {R : Type} [CommRing R]

lemma wlocal_good_of_factor {r n : ℕ} {hn : n ≤ r} {ν : Fin n → ℕ} {M Q Q' : Matrix (Fin r) (Fin r) R}
    (hQ : wlocal_Good hn ν Q) (hQQ : Q * Q' = 1) (h : wlocal_Good hn ν (Q' * M)) :
    wlocal_Good hn ν M := by
  have hM : M = Q * (Q' * M) := by
    rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  rw [hM]
  exact wlocal_good_mul hQ h

variable [IsLocalRing R]

lemma wlocal_unit_add {a b : R} (ha : ¬IsUnit a) (hb : IsUnit b) : IsUnit (a + b) := by
  by_contra h
  have h1 : (a + b) + (-a) ∈ nonunits R :=
    IsLocalRing.nonunits_add (mem_nonunits_iff.mpr h)
      (mem_nonunits_iff.mpr fun hu => ha (by simpa using hu.neg))
  have h2 : (a + b) + (-a) = b := by ring
  rw [h2] at h1
  exact mem_nonunits_iff.mp h1 hb

lemma wlocal_pivot {r : ℕ} (k : Fin r) (M N : Matrix (Fin r) (Fin r) R) (hNM : N * M = 1)
    (hstd : ∀ i j : Fin r, j.val < k.val → M i j = if i = j then 1 else 0) :
    ∃ i : Fin r, k.val ≤ i.val ∧ IsUnit (M i k) := by
  by_contra hcon
  push_neg at hcon
  have hNcol : ∀ j : Fin r, j.val < k.val → N k j = 0 := by
    intro j hj
    have h1 : (N * M) k j = 0 := by
      rw [hNM, Matrix.one_apply_ne]
      intro h
      rw [h] at hj
      exact lt_irrefl _ hj
    rw [Matrix.mul_apply] at h1
    have h2 : ∑ l, N k l * M l j = N k j := by
      rw [Finset.sum_eq_single j]
      · rw [hstd j j hj, if_pos rfl, mul_one]
      · intro l _ hl
        rw [hstd l j hj, if_neg hl, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [← h2]
    exact h1
  have hsum : (N * M) k k ∈ IsLocalRing.maximalIdeal R := by
    rw [Matrix.mul_apply]
    apply Ideal.sum_mem
    intro l _
    by_cases hl : l.val < k.val
    · rw [hNcol l hl, zero_mul]
      exact Ideal.zero_mem _
    · apply Ideal.mul_mem_left
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hcon l (not_lt.mp hl)))
  rw [hNM, Matrix.one_apply_eq] at hsum
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hsum)) isUnit_one

private lemma mul_mul_mul_eq_one_of_inverses {r : ℕ} {N M A B : Matrix (Fin r) (Fin r) R} (h : N * M = 1)
    (hBA : B * A = 1) : N * B * (A * M) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc B A M, hBA, Matrix.one_mul, h]

theorem wlocal_main {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    ∀ d k : ℕ, k + d = r → ∀ M N : Matrix (Fin r) (Fin r) R, N * M = 1 →
      (∀ i j : Fin r, j.val < k → M i j = if i = j then 1 else 0) → wlocal_Good hn ν M := by
  intro d
  induction d with
  | zero =>
    intro k hk M N _ hstd
    have hM : M = 1 := by
      ext i j
      rw [hstd i j (by have := j.isLt; omega), Matrix.one_apply]
    rw [hM]
    exact wlocal_good_one hn ν
  | succ d ih =>
    intro k hk M N hNM hstd
    have hkr : k < r := by omega
    obtain ⟨kk, hkk⟩ : ∃ kk : Fin r, kk.val = k := ⟨⟨k, hkr⟩, rfl⟩
    have cont : ∀ P P' : Matrix (Fin r) (Fin r) R, P' * P = 1 → wlocal_Good hn ν P' →
        IsUnit ((P * M) kk kk) →
        (∀ l j : Fin r, j.val < k → (P * M) l j = if l = j then 1 else 0) → wlocal_Good hn ν M := by
      intro P P' hPP hP' hunit hstd1
      obtain ⟨u, hu⟩ := hunit
      obtain ⟨M1, hM1⟩ : ∃ M1, M1 = P * M := ⟨_, rfl⟩
      rw [← hM1] at hu hstd1
      obtain ⟨M2, hM2⟩ : ∃ M2, M2 = wlocal_E kk kk ((↑u⁻¹ : R) - 1) * M1 := ⟨_, rfl⟩
      have h2 : ∀ l j : Fin r, M2 l j = M1 l j + (if l = kk then ((↑u⁻¹ : R) - 1) * M1 kk j else 0) := by
        intro l j
        rw [hM2, wlocal_E_mul_apply]
      have h2kk : M2 kk kk = 1 := by
        rw [h2, if_pos rfl, ← hu]
        linear_combination (Units.inv_mul u)
      have h2std : ∀ l j : Fin r, j.val < k → M2 l j = if l = j then 1 else 0 := by
        intro l j hj
        have hkj : kk ≠ j := by
          intro h
          rw [← h] at hj
          omega
        rw [h2, hstd1 l j hj, hstd1 kk j hj, if_neg hkj, mul_zero, ite_self, add_zero]
      obtain ⟨M3, hM3⟩ : ∃ M3, M3 = wlocal_L kk (fun l => -(M2 l kk)) * M2 := ⟨_, rfl⟩
      have h3 : ∀ l j : Fin r, M3 l j = M2 l j + (if l ≠ kk then -(M2 l kk) * M2 kk j else 0) := by
        intro l j
        rw [hM3, wlocal_L_mul_apply]
      have h3std : ∀ l j : Fin r, j.val < k + 1 → M3 l j = if l = j then 1 else 0 := by
        intro l j hj
        rw [h3]
        by_cases hjk : j.val < k
        · have hkj : kk ≠ j := by
            intro h
            rw [← h] at hjk
            omega
          rw [h2std l j hjk, h2std kk j hjk, if_neg hkj, mul_zero, ite_self, add_zero]
        · have hj' : j = kk := by
            apply Fin.ext
            omega
          rw [hj', h2kk, mul_one]
          by_cases hl : l = kk
          · simp [hl, h2kk]
          · rw [if_pos hl, if_neg hl]
            ring
      have hLL : wlocal_L kk (fun l => M2 l kk) * wlocal_L kk (fun l => -(M2 l kk)) = 1 := by
        rw [wlocal_L_mul_L]
        have h0 : ((fun l => M2 l kk) + fun l => -(M2 l kk)) = (0 : Fin r → R) := by
          funext l
          simp
        rw [h0, wlocal_L_one]
      have hEE : wlocal_E kk kk ((u : R) - 1) * wlocal_E kk kk ((↑u⁻¹ : R) - 1) = 1 := by
        rw [wlocal_E_mul_E, if_pos rfl,
          show ((u : R) - 1) + ((↑u⁻¹ : R) - 1) + ((u : R) - 1) * ((↑u⁻¹ : R) - 1) = 0 by
            linear_combination (Units.mul_inv u),
          wlocal_E_zero]
      have hN1 : N * P' * M1 = 1 := by
        rw [hM1]
        exact mul_mul_mul_eq_one_of_inverses hNM hPP
      have hN2 : N * P' * wlocal_E kk kk ((u : R) - 1) * M2 = 1 := by
        rw [hM2]
        exact mul_mul_mul_eq_one_of_inverses hN1 hEE
      have hN3 : N * P' * wlocal_E kk kk ((u : R) - 1) * wlocal_L kk (fun l => M2 l kk) * M3 = 1 := by
        rw [hM3]
        exact mul_mul_mul_eq_one_of_inverses hN2 hLL
      have hM3g : wlocal_Good hn ν M3 := ih (k + 1) (by omega) M3 _ hN3 h3std
      have hM2g : wlocal_Good hn ν M2 :=
        wlocal_good_of_factor (wlocal_good_L hn ν kk (fun l => M2 l kk)) hLL (by rw [← hM3]; exact hM3g)
      have hM1g : wlocal_Good hn ν M1 :=
        wlocal_good_of_factor (wlocal_good_E hn ν kk kk ((u : R) - 1)) hEE (by rw [← hM2]; exact hM2g)
      exact wlocal_good_of_factor hP' hPP (by rw [← hM1]; exact hM1g)
    by_cases hu0 : IsUnit (M kk kk)
    · refine cont 1 1 (Matrix.one_mul 1) (wlocal_good_one hn ν) ?_ ?_
      · rw [Matrix.one_mul]
        exact hu0
      · intro l j hj
        rw [Matrix.one_mul]
        exact hstd l j hj
    · obtain ⟨i, hki, hiu⟩ := wlocal_pivot kk M N hNM (by intro i j hj; exact hstd i j (by omega))
      have hik : i ≠ kk := by
        intro h
        rw [h] at hiu
        exact hu0 hiu
      refine cont (wlocal_E kk i 1) (wlocal_E kk i (-1)) ?_ (wlocal_good_E hn ν kk i (-1)) ?_ ?_
      · rw [wlocal_E_mul_E, if_neg (Ne.symm hik), show (-1 : R) + 1 + 0 = 0 by ring, wlocal_E_zero]
      · rw [wlocal_E_mul_apply, if_pos rfl, one_mul]
        exact wlocal_unit_add hu0 hiu
      · intro l j hj
        have hij : i ≠ j := by
          intro h
          rw [← h] at hj
          omega
        rw [wlocal_E_mul_apply, hstd i j hj, if_neg hij, mul_zero, ite_self, add_zero]
        exact hstd l j hj

end

theorem wlocal_local : Formalism.UG.WeylGLStableLocal := by
  intro R _ _ r n hn ν g f hf
  exact wlocal_main hn ν r 0 (by omega) _ _ (Units.mul_inv g) (fun i j hj => absurd hj (Nat.not_lt_zero _)) f hf

section

variable {R S : Type} [CommRing R] [CommRing S]

lemma wlocal_map_rowGen (φ : R →+* S) {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowGen S a b (map φ f) = Polynomial.map (map φ) (rowGen R a b f) := by
  have key : ((rowGen S a b).toRingHom.comp (map φ) : MvPolynomial (Fin r × Fin n) R →+* _) =
      (Polynomial.mapRingHom (map φ)).comp (rowGen R a b).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    · intro v
      by_cases h : v.1 = b <;> simp [rowGen, h]
  exact RingHom.congr_fun key f

lemma wlocal_map_rowDiv (φ : R →+* S) {r n : ℕ} (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (rowDiv R a b k f) = rowDiv S a b k (map φ f) := by
  unfold rowDiv
  rw [wlocal_map_rowGen, Polynomial.coeff_map]

lemma wlocal_map_applyWord (φ : R →+* S) {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (applyWord R w f) = applyWord S w (map φ f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show map φ (rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f)) =
      rowDiv S x.1 x.2.1 x.2.2 (applyWord S w (map φ f))
    rw [wlocal_map_rowDiv, ih]

lemma wlocal_map_lpMinor (φ : R →+* S) {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    map φ (lpMinor R (r := r) (n := n) s hr hn) = lpMinor S s hr hn := by
  unfold lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

lemma wlocal_map_hw (φ : R →+* S) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    map φ (hw R hn ν) = hw S hn ν := by
  unfold hw
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, wlocal_map_lpMinor]

lemma wlocal_map_smul (φ : R →+* S) {σ : Type} (a : R) (y : MvPolynomial σ R) :
    map φ (a • y) = φ a • map φ y := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C]

lemma wlocal_map_weyl (φ : R →+* S) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) :
    map φ f ∈ weyl S r n hn ν := by
  unfold weyl at hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro x hx
    obtain ⟨w, rfl⟩ := hx
    rw [wlocal_map_applyWord, wlocal_map_hw]
    unfold weyl
    exact Submodule.subset_span ⟨w, rfl⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro m x _ hx
    rw [wlocal_map_smul]
    exact Submodule.smul_mem _ _ hx

lemma wlocal_map_rowAct (φ : R →+* S) {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (rowAct R g f) = rowAct S (g.map φ) (map φ f) := by
  have key : (map φ).comp (rowAct R (n := n) g).toRingHom =
      (rowAct S (n := n) (g.map φ)).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [rowAct, MvPolynomial.algebraMap_eq]
    · intro v
      simp [rowAct, Matrix.map_apply]
  exact RingHom.congr_fun key f

end

section

variable {R : Type} [CommRing R]

lemma wlocal_kill (P : Ideal R) [P.IsPrime] {σ : Type} (w : MvPolynomial σ R)
    (hw : map (algebraMap R (Localization.AtPrime P)) w = 0) :
    ∃ t ∈ P.primeCompl, C t * w = 0 := by
  classical
  have hc : ∀ m, ∃ t : P.primeCompl, (t : R) * w.coeff m = 0 := by
    intro m
    have h1 : algebraMap R (Localization.AtPrime P) (w.coeff m) = 0 := by
      have := congrArg (coeff m) hw
      rwa [coeff_map, coeff_zero] at this
    exact (IsLocalization.map_eq_zero_iff P.primeCompl (Localization.AtPrime P) _).mp h1
  choose t ht using hc
  refine ⟨∏ m ∈ w.support, (t m : R), Submonoid.prod_mem _ (fun m _ => (t m).2), ?_⟩
  ext m
  rw [coeff_C_mul, coeff_zero]
  by_cases hm : m ∈ w.support
  · rw [← Finset.mul_prod_erase _ _ hm, mul_comm ((t m : P.primeCompl) : R), mul_assoc, ht m, mul_zero]
  · have h0 : w.coeff m = 0 := by
      by_contra h
      exact hm (mem_support_iff.mpr h)
    rw [h0, mul_zero]

lemma wlocal_loc (P : Ideal R) [P.IsPrime] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (x : MvPolynomial (Fin r × Fin n) R)
    (hx : map (algebraMap R (Localization.AtPrime P)) x ∈ weyl (Localization.AtPrime P) r n hn ν) :
    ∃ t ∈ P.primeCompl, C t * x ∈ weyl R r n hn ν := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R →+* Localization.AtPrime P, φ = algebraMap R (Localization.AtPrime P) :=
    ⟨_, rfl⟩
  rw [← hφ] at hx
  have key : ∀ y ∈ weyl (Localization.AtPrime P) r n hn ν,
      ∃ s ∈ P.primeCompl, ∃ z ∈ weyl R r n hn ν, φ s • y = map φ z := by
    intro y hy
    unfold weyl at hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro y' hy'
      obtain ⟨w, rfl⟩ := hy'
      refine ⟨1, P.primeCompl.one_mem, applyWord R w (hw R hn ν), ?_, ?_⟩
      · unfold weyl
        exact Submodule.subset_span ⟨w, rfl⟩
      · rw [map_one, one_smul, wlocal_map_applyWord, wlocal_map_hw]
    · exact ⟨1, P.primeCompl.one_mem, 0, Submodule.zero_mem _, by simp⟩
    · intro y1 y2 _ _ h1 h2
      obtain ⟨s1, hs1, z1, hz1, e1⟩ := h1
      obtain ⟨s2, hs2, z2, hz2, e2⟩ := h2
      refine ⟨s1 * s2, P.primeCompl.mul_mem hs1 hs2, s2 • z1 + s1 • z2,
        Submodule.add_mem _ (Submodule.smul_mem _ _ hz1) (Submodule.smul_mem _ _ hz2), ?_⟩
      rw [map_add, wlocal_map_smul, wlocal_map_smul, ← e1, ← e2]
      simp only [MvPolynomial.smul_eq_C_mul, map_mul]
      ring
    · intro a y' _ h
      obtain ⟨s, hs, z, hz, e⟩ := h
      obtain ⟨⟨b, s'⟩, hbs0⟩ := IsLocalization.mk'_surjective P.primeCompl a
      have hbs : IsLocalization.mk' (Localization.AtPrime P) b s' = a := hbs0
      refine ⟨(s' : R) * s, P.primeCompl.mul_mem s'.2 hs, b • z, Submodule.smul_mem _ _ hz, ?_⟩
      have hspec : φ (s' : R) * IsLocalization.mk' (Localization.AtPrime P) b s' = φ b := by
        rw [hφ]
        first
        | exact IsLocalization.mk'_spec' (S := Localization.AtPrime P) b s'
        | simp
      rw [wlocal_map_smul, ← e, ← hbs, ← hspec, map_mul, smul_smul, smul_smul]
      congr 1
      ring
  obtain ⟨s, hs, z, hz, e⟩ := key _ hx
  have h0 : map φ (C s * x - z) = 0 := by
    rw [map_sub, map_mul, map_C, ← e, MvPolynomial.smul_eq_C_mul, sub_self]
  obtain ⟨t, ht, htz⟩ := wlocal_kill P (C s * x - z) (by rw [← hφ]; exact h0)
  refine ⟨t * s, P.primeCompl.mul_mem ht hs, ?_⟩
  have h1 : C (t * s) * x = t • z := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul]
    linear_combination htz
  rw [h1]
  exact Submodule.smul_mem _ _ hz

end

theorem wlocal_global : Formalism.UG.WeylGLStable := by
  intro R _ r n hn ν g f hf
  obtain ⟨J, hJdef⟩ : ∃ J : Ideal R,
      J = Submodule.comap (LinearMap.toSpanSingleton R _ (dwAct R r n g f)) (weyl R r n hn ν) := ⟨_, rfl⟩
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J hne
    haveI := hPmax.isPrime
    have hf' := wlocal_map_weyl (algebraMap R (Localization.AtPrime P)) hn ν f hf
    have hloc := wlocal_local (Localization.AtPrime P) r n hn ν
      (Units.map (algebraMap R (Localization.AtPrime P)).mapMatrix.toMonoidHom g) _ hf'
    have hg : ((Units.map (algebraMap R (Localization.AtPrime P)).mapMatrix.toMonoidHom g)⁻¹ :
        GL (Fin r) (Localization.AtPrime P)).val =
        (g⁻¹ : GL (Fin r) R).val.map (algebraMap R (Localization.AtPrime P)) := by
      first
      | rfl
      | simp [Units.coe_map_inv, RingHom.mapMatrix_apply]
    have hmem : map (algebraMap R (Localization.AtPrime P)) (dwAct R r n g f) ∈
        weyl (Localization.AtPrime P) r n hn ν := by
      unfold dwAct at hloc ⊢
      rw [hg, ← wlocal_map_rowAct] at hloc
      exact hloc
    obtain ⟨t, ht, hty⟩ := wlocal_loc P hn ν _ hmem
    have htJ : t ∈ J := by
      rw [hJdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, MvPolynomial.smul_eq_C_mul]
      exact hty
    exact (Ideal.mem_primeCompl_iff.mp ht) (hJP htJ)
  have h1 : (1 : R) ∈ J := by
    rw [hJ]
    exact Submodule.mem_top
  rw [hJdef, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul] at h1
  exact h1

theorem weyl_module_GL_stable_local : Formalism.UG.WeylGLStableLocal := wlocal_local

theorem weyl_module_GL_stable : Formalism.UG.WeylGLStable := wlocal_global

end Formalism.UG.P
