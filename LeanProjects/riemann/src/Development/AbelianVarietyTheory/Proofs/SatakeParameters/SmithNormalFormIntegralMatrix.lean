import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat

noncomputable section
open Matrix

namespace GlobalTheory.Hk3.Smith

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_intL {a : L} : a ∈ Formalism.UG.intL L ↔ Valued.v a ≤ 1 := by
  unfold Formalism.UG.intL; exact Valuation.mem_integer_iff _ _

def IsUnimod {k : ℕ} (P : Matrix (Fin k) (Fin k) L) : Prop :=
  (∀ i j, P i j ∈ Formalism.UG.intL L) ∧
    ∃ P' : Matrix (Fin k) (Fin k) L, (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1

theorem mul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) :
    ∀ i j, (A * B) i j ∈ Formalism.UG.intL L := fun i j => by
  rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem one_int {k : ℕ} : ∀ i j, (1 : Matrix (Fin k) (Fin k) L) i j ∈ Formalism.UG.intL L := by
  intro i j; rw [Matrix.one_apply]; split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem isUnimod_one {k : ℕ} : IsUnimod (1 : Matrix (Fin k) (Fin k) L) :=
  ⟨one_int, 1, one_int, by simp⟩

theorem IsUnimod.mul {k : ℕ} {P Q : Matrix (Fin k) (Fin k) L} (hP : IsUnimod P) (hQ : IsUnimod Q) :
    IsUnimod (P * Q) := by
  obtain ⟨hP1, P', hP', hPP⟩ := hP
  obtain ⟨hQ1, Q', hQ', hQQ⟩ := hQ
  refine ⟨mul_int hP1 hQ1, Q' * P', mul_int hQ' hP', ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQQ, Matrix.one_mul, hPP]

theorem perm_mul_left {k n : ℕ} (σ : Equiv.Perm (Fin k)) (x : Matrix (Fin k) (Fin n) L) :
    (1 : Matrix (Fin k) (Fin k) L).submatrix σ id * x = x.submatrix σ id := by
  ext i j; simp [Matrix.mul_apply, Matrix.one_apply]

theorem perm_mul_right {k n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Matrix (Fin k) (Fin n) L) :
    x * (1 : Matrix (Fin n) (Fin n) L).submatrix id σ = x.submatrix id σ := by
  ext i j; simp [Matrix.mul_apply, Matrix.one_apply]

theorem isUnimod_permL {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    IsUnimod ((1 : Matrix (Fin k) (Fin k) L).submatrix σ id) := by
  refine ⟨fun i j => one_int _ _, (1 : Matrix (Fin k) (Fin k) L).submatrix σ.symm id, fun i j => one_int _ _, ?_⟩
  rw [perm_mul_left]; ext i j
  exact congrArg (fun t => (1 : Matrix (Fin k) (Fin k) L) t j) (σ.symm_apply_apply i)

theorem isUnimod_permR {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    IsUnimod ((1 : Matrix (Fin k) (Fin k) L).submatrix id σ) := by
  refine ⟨fun i j => one_int _ _, (1 : Matrix (Fin k) (Fin k) L).submatrix id σ.symm, fun i j => one_int _ _, ?_⟩
  rw [perm_mul_right]; ext i j
  exact congrArg (fun t => (1 : Matrix (Fin k) (Fin k) L) i t) (σ.apply_symm_apply j)

def blk {m n : ℕ} (a : L) (A : Matrix (Fin m) (Fin n) L) : Matrix (Fin (m+1)) (Fin (n+1)) L :=
  Matrix.of fun i j => Fin.cases (Fin.cases a (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

@[simp] theorem blk_zero_zero {m n : ℕ} (a : L) (A : Matrix (Fin m) (Fin n) L) : blk a A 0 0 = a := rfl
@[simp] theorem blk_zero_succ {m n : ℕ} (a : L) (A : Matrix (Fin m) (Fin n) L) (j : Fin n) :
    blk a A 0 j.succ = 0 := rfl
@[simp] theorem blk_succ_zero {m n : ℕ} (a : L) (A : Matrix (Fin m) (Fin n) L) (i : Fin m) :
    blk a A i.succ 0 = 0 := rfl
@[simp] theorem blk_succ_succ {m n : ℕ} (a : L) (A : Matrix (Fin m) (Fin n) L) (i : Fin m) (j : Fin n) :
    blk a A i.succ j.succ = A i j := rfl

theorem blk_mul {m n k : ℕ} (a b : L) (A : Matrix (Fin m) (Fin n) L) (B : Matrix (Fin n) (Fin k) L) :
    blk a A * blk b B = blk (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem blk_one {m : ℕ} : blk (1 : L) (1 : Matrix (Fin m) (Fin m) L) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem isUnimod_blk {m : ℕ} {P : Matrix (Fin m) (Fin m) L} (hP : IsUnimod P) : IsUnimod (blk (1 : L) P) := by
  obtain ⟨hP1, P', hP', hPP⟩ := hP
  have hint : ∀ {A : Matrix (Fin m) (Fin m) L}, (∀ i j, A i j ∈ Formalism.UG.intL L) →
      ∀ i j, blk (1 : L) A i j ∈ Formalism.UG.intL L := by
    intro A hA i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [Subring.one_mem, Subring.zero_mem, hA]
  exact ⟨hint hP1, blk 1 P', hint hP', by rw [blk_mul, hPP, one_mul, blk_one]⟩

def IsDiagF {m n : ℕ} (z : Matrix (Fin m) (Fin n) L) : Prop :=
  ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ (j : ℕ) → z i j = 0

theorem nilp_unimod {k : ℕ} (A : Matrix (Fin k) (Fin k) L) (hA : ∀ i j, A i j ∈ Formalism.UG.intL L)
    (hAA : A * A = 0) : IsUnimod (1 - A) := by
  refine ⟨fun i j => by rw [Matrix.sub_apply]; exact Subring.sub_mem _ (one_int i j) (hA i j), 1 + A,
    fun i j => by rw [Matrix.add_apply]; exact Subring.add_mem _ (one_int i j) (hA i j), ?_⟩
  rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hAA]
  abel

theorem div_int {a p : L} (hp : p ≠ 0) (h : Valued.v a ≤ Valued.v p) : a / p ∈ Formalism.UG.intL L := by
  rw [mem_intL, map_div₀]
  have : 0 < Valued.v p := (Valuation.pos_iff _).2 hp
  exact (div_le_one₀ this).2 h

theorem clear {m n : ℕ} (x : Matrix (Fin (m+1)) (Fin (n+1)) L) (hp : x 0 0 ≠ 0)
    (hmax : ∀ i j, Valued.v (x i j) ≤ Valued.v (x 0 0)) :
    ∃ (R : Matrix (Fin (m+1)) (Fin (m+1)) L) (C : Matrix (Fin (n+1)) (Fin (n+1)) L), IsUnimod R ∧ IsUnimod C ∧
      R * x * C = blk (x 0 0) (Matrix.of fun i j => (R * x * C) i.succ j.succ) := by
  set p := x 0 0 with hpdef
  let A : Matrix (Fin (m+1)) (Fin (m+1)) L := Matrix.of fun i j => if i ≠ 0 ∧ j = 0 then x i 0 / p else 0
  let B : Matrix (Fin (n+1)) (Fin (n+1)) L := Matrix.of fun i j => if i = 0 ∧ j ≠ 0 then x 0 j / p else 0
  have hAi : ∀ i j, A i j ∈ Formalism.UG.intL L := by
    intro i j; simp only [A, Matrix.of_apply]; split_ifs
    · exact div_int hp (hmax _ _)
    · exact Subring.zero_mem _
  have hBi : ∀ i j, B i j ∈ Formalism.UG.intL L := by
    intro i j; simp only [B, Matrix.of_apply]; split_ifs
    · exact div_int hp (hmax _ _)
    · exact Subring.zero_mem _
  have hAA : A * A = 0 := by
    ext i j; simp only [Matrix.mul_apply, A, Matrix.of_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero; intro k _; by_cases hk : k = 0 <;> simp [hk]
  have hBB : B * B = 0 := by
    ext i j; simp only [Matrix.mul_apply, B, Matrix.of_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero; intro k _; by_cases hk : k = 0 <;> simp [hk]
  have hy : ∀ i j, ((1 - A) * x : Matrix (Fin (m+1)) (Fin (n+1)) L) i j = x i j - (if i ≠ 0 then x i 0 / p * x 0 j else 0) := by
    intro i j
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply]
    congr 1
    rw [Finset.sum_eq_single 0]
    · by_cases hi : i = 0 <;> simp [A, hi]
    · intro k _ hk; simp [A, hk]
    · simp
  set y : Matrix (Fin (m+1)) (Fin (n+1)) L := (1 - A) * x with hydef
  have hz : ∀ i j, (y * (1 - B) : Matrix (Fin (m+1)) (Fin (n+1)) L) i j =
      y i j - (if j ≠ 0 then y i 0 * (x 0 j / p) else 0) := by
    intro i j
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.mul_apply]
    congr 1
    rw [Finset.sum_eq_single 0]
    · by_cases hj : j = 0 <;> simp [B, hj]
    · intro k _ hk; simp [B, hk]
    · simp
  refine ⟨1 - A, 1 - B, nilp_unimod A hAi hAA, nilp_unimod B hBi hBB, ?_⟩
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · rw [hz, hy]; simp [p]
  · rw [hz, hy, hy]; simp [Fin.succ_ne_zero, p]; rw [mul_div_cancel₀ _ (show x 0 0 ≠ 0 from hp), sub_self]
  · rw [hz, hy]; simp [Fin.succ_ne_zero, p]; rw [div_mul_cancel₀ _ (show x 0 0 ≠ 0 from hp), sub_self]
  · simp

theorem exists_diag : ∀ (m n : ℕ) (x : Matrix (Fin m) (Fin n) L),
    ∃ (P : Matrix (Fin m) (Fin m) L) (Q : Matrix (Fin n) (Fin n) L),
      IsUnimod P ∧ IsUnimod Q ∧ IsDiagF (P * x * Q) := by
  intro m
  induction m with
  | zero => intro n x; exact ⟨1, 1, isUnimod_one, isUnimod_one, fun i => i.elim0⟩
  | succ m ih =>
    intro n x
    cases n with
    | zero => exact ⟨1, 1, isUnimod_one, isUnimod_one, fun _ j => j.elim0⟩
    | succ n =>
      by_cases hx : ∀ i j, x i j = 0
      · refine ⟨1, 1, isUnimod_one, isUnimod_one, fun i j _ => ?_⟩
        simp [hx i j]
      push_neg at hx
      obtain ⟨i0, j0, hx0⟩ := hx
      obtain ⟨⟨r, c⟩, -, hrc⟩ := Finset.exists_max_image Finset.univ
        (fun q : Fin (m+1) × Fin (n+1) => Valued.v (x q.1 q.2)) ⟨(i0, j0), Finset.mem_univ _⟩
      set x1 : Matrix (Fin (m+1)) (Fin (n+1)) L := x.submatrix (Equiv.swap 0 r) (Equiv.swap 0 c) with hx1
      have h00 : x1 0 0 = x r c := by simp [x1, Equiv.swap_apply_left]
      have hp : x1 0 0 ≠ 0 := by
        rw [h00]; intro h
        have h2 : Valued.v (x i0 j0) ≤ Valued.v (x r c) := hrc (i0, j0) (Finset.mem_univ _)
        rw [h, map_zero, le_zero_iff, Valuation.zero_iff] at h2
        exact hx0 h2
      have hmax : ∀ i j, Valued.v (x1 i j) ≤ Valued.v (x1 0 0) := by
        intro i j; rw [h00]
        exact hrc (Equiv.swap 0 r i, Equiv.swap 0 c j) (Finset.mem_univ _)
      obtain ⟨R, C, hR, hC, hz⟩ := clear x1 hp hmax
      set w : Matrix (Fin m) (Fin n) L := Matrix.of fun (i : Fin m) (j : Fin n) => (R * x1 * C) i.succ j.succ with hw
      obtain ⟨P0, Q0, hP0, hQ0, hD⟩ := ih n w
      refine ⟨blk 1 P0 * R * (1 : Matrix (Fin (m+1)) (Fin (m+1)) L).submatrix (Equiv.swap 0 r) id,
        (1 : Matrix (Fin (n+1)) (Fin (n+1)) L).submatrix id (Equiv.swap 0 c) * C * blk 1 Q0,
        ((isUnimod_blk hP0).mul hR).mul (isUnimod_permL _),
        ((isUnimod_permR _).mul hC).mul (isUnimod_blk hQ0), ?_⟩
      have hsw : (1 : Matrix (Fin (m+1)) (Fin (m+1)) L).submatrix (Equiv.swap 0 r) id * x *
          (1 : Matrix (Fin (n+1)) (Fin (n+1)) L).submatrix id (Equiv.swap 0 c) = x1 := by
        rw [perm_mul_left, perm_mul_right]; rfl
      have heq : blk 1 P0 * R * (1 : Matrix (Fin (m+1)) (Fin (m+1)) L).submatrix (Equiv.swap 0 r) id * x *
          ((1 : Matrix (Fin (n+1)) (Fin (n+1)) L).submatrix id (Equiv.swap 0 c) * C * blk 1 Q0) =
          blk (x1 0 0) (P0 * w * Q0) := by
        calc _ = blk 1 P0 * (R * ((1 : Matrix (Fin (m+1)) (Fin (m+1)) L).submatrix (Equiv.swap 0 r) id * x *
              (1 : Matrix (Fin (n+1)) (Fin (n+1)) L).submatrix id (Equiv.swap 0 c)) * C) * blk 1 Q0 := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hsw, hz, blk_mul, blk_mul, one_mul, mul_one]
      rw [heq]
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij
      · exact absurd rfl hij
      · simp
      · simp
      · simp only [blk_succ_succ]
        exact hD i j (by simpa [Fin.val_succ] using hij)

theorem v_inv_pow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (k : ℕ) :
    Valued.v (ϖ⁻¹ ^ k) = ((Multiplicative.ofAdd (k : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_pow, map_inv₀, hϖ, ← WithZero.coe_inv, ← WithZero.coe_pow, ← ofAdd_neg, neg_neg, ← ofAdd_nsmul,
    nsmul_eq_mul, mul_one]

theorem v_eq_ord {y : L} (hy : y ≠ 0) :
    Valued.v y = ((Multiplicative.ofAdd (-Formalism.UG.ordL y) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  unfold Formalism.UG.ordL
  rw [dif_neg h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

end GlobalTheory.Hk3.Smith

open GlobalTheory.Hk3.Smith in

theorem GlobalTheory.Hk3.smith_int_approx : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L),
    ∃ (P P' : Matrix (Fin n') (Fin n') L) (Q Q' : Matrix (Fin n) (Fin n) L) (a : Fin n' → ℕ),
      (∀ i j, P i j ∈ Formalism.UG.intL L) ∧ (∀ i j, P' i j ∈ Formalism.UG.intL L) ∧ P * P' = 1 ∧
      (∀ i j, Q i j ∈ Formalism.UG.intL L) ∧ (∀ i j, Q' i j ∈ Formalism.UG.intL L) ∧ Q * Q' = 1 ∧
      ∀ i j, (P * x * Q - Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ hϖ n n' x
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  obtain ⟨P, Q, hP, hQ, hD⟩ := exists_diag n' n x
  set z := P * x * Q with hzdef
  let d : Fin n' → L := fun i => if h : (i : ℕ) < n then z i ⟨i, h⟩ else 0
  let a : Fin n' → ℕ := fun i => (-Formalism.UG.ordL (d i)).toNat
  let s : Fin n' → L := fun i => if 0 < a i then ϖ⁻¹ ^ a i / d i else 1
  let t : Fin n' → L := fun i => if 0 < a i then d i / ϖ⁻¹ ^ a i else 1
  have hdne : ∀ i, 0 < a i → d i ≠ 0 := by
    intro i h hd; simp [a, hd, Formalism.UG.ordL] at h
  have hva : ∀ i, 0 < a i → Valued.v (ϖ⁻¹ ^ a i) = Valued.v (d i) := by
    intro i h
    rw [v_inv_pow hϖ, v_eq_ord (hdne i h)]
    have h' := Int.lt_toNat.mp h
    simp only [a]
    rw [Int.toNat_of_nonneg (by omega)]
  have hpw : ∀ k : ℕ, ϖ⁻¹ ^ k ≠ 0 := fun k => pow_ne_zero _ (inv_ne_zero hϖ0)
  have hS : IsUnimod (Matrix.diagonal s) := by
    refine ⟨fun i j => ?_, Matrix.diagonal t, fun i j => ?_, ?_⟩
    · rw [Matrix.diagonal_apply]; split_ifs with hij
      · simp only [s]; split_ifs with ha
        · rw [mem_intL, map_div₀, hva i ha, div_self ((Valuation.ne_zero_iff _).2 (hdne i ha))]
        · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · rw [Matrix.diagonal_apply]; split_ifs with hij
      · simp only [t]; split_ifs with ha
        · rw [mem_intL, map_div₀, hva i ha, div_self ((Valuation.ne_zero_iff _).2 (hdne i ha))]
        · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i; simp only [s, t, Pi.one_apply]; split_ifs with ha
      · rw [div_mul_div_comm, mul_comm (ϖ⁻¹ ^ a i), div_self (mul_ne_zero (hdne i ha) (hpw _))]
      · exact one_mul 1
  obtain ⟨hPi, P', hP'i, hPP'⟩ := hS.mul hP
  obtain ⟨hQi, Q', hQ'i, hQQ'⟩ := hQ
  refine ⟨Matrix.diagonal s * P, P', Q, Q', a, hPi, hP'i, hPP', hQi, hQ'i, hQQ', ?_⟩
  intro i j
  have hmul : Matrix.diagonal s * P * x * Q = Matrix.diagonal s * z := by
    rw [hzdef]; simp only [Matrix.mul_assoc]
  rw [hmul, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases hij : (i : ℕ) = (j : ℕ)
  · have hi : (i : ℕ) < n := hij ▸ j.isLt
    have hj : j = ⟨i, hi⟩ := Fin.ext hij.symm
    have hzd : z i j = d i := by simp only [d, dif_pos hi, hj]
    rw [hzd]
    by_cases ha : 0 < a i
    · rw [if_pos ⟨hij, ha⟩]
      simp only [s, if_pos ha]
      rw [div_mul_cancel₀ _ (hdne i ha), sub_self]
      exact Subring.zero_mem _
    · rw [if_neg (fun h => ha h.2), sub_zero]
      simp only [s, if_neg ha, one_mul]
      by_cases hd0 : d i = 0
      · rw [hd0]; exact Subring.zero_mem _
      · rw [mem_intL, v_eq_ord hd0]
        have h0 : (-Formalism.UG.ordL (d i)).toNat = 0 := by simpa [a] using ha
        rw [Int.toNat_eq_zero] at h0
        rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
        exact h0
  · rw [hD i j hij, if_neg (fun h => hij h.1), mul_zero, sub_zero]
    exact Subring.zero_mem _
