import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns

namespace GlobalTheory.HatTaylorPlus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Polynomial

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def ev (f : ℕ → A) (P : A[X]) : A := P.sum fun j a => f j * a

omit [Algebra ℂ A] in
theorem ev_add (f : ℕ → A) (P Q : A[X]) : ev f (P + Q) = ev f P + ev f Q :=
  Polynomial.sum_add_index _ _ _ (by simp) (by simp [mul_add])

omit [Algebra ℂ A] in
theorem ev_monomial (f : ℕ → A) (n : ℕ) (a : A) : ev f (monomial n a) = f n * a :=
  Polynomial.sum_monomial_index _ _ (by simp)

omit [Algebra ℂ A] in
theorem ev_mul (f g : ℕ → A) (P Q : A[X]) (z : A) (h : ∀ j, z * g j = ev (fun i => f (j + i)) P) :
    z * ev g Q = ev f (P * Q) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [ev_add, mul_add, mul_add, ev_add, hp, hq]
  | monomial n b =>
    rw [ev_monomial, ← mul_assoc, h]
    clear h
    induction P using Polynomial.induction_on' with
    | add p q hp hq => rw [ev_add, add_mul, add_mul, ev_add, hp, hq]
    | monomial k a => rw [monomial_mul_monomial, ev_monomial, ev_monomial, mul_assoc, add_comm]

omit [Algebra ℂ A] in
theorem ev_eq_sum (f : ℕ → A) (P : A[X]) (n : ℕ) (h : P.natDegree < n) :
    ev f P = ∑ j ∈ Finset.range n, f j * P.coeff j :=
  Polynomial.sum_over_range' _ (by simp) n h

omit [Algebra ℂ A] in
theorem mul_ev (z : A) (f : ℕ → A) (P : A[X]) : z * ev f P = ev (fun i => z * f i) P := by
  simp [ev, Polynomial.sum, Finset.mul_sum, mul_assoc]

def Deg (L : LevelData A r) (Y : ℂ) (D : ℕ) (Z : ℂ → A) : Prop :=
  ∃ P : A[X], P.natDegree ≤ D ∧ (∀ s : ℂ, Z (Y + s) = ev (fun j => algebraMap ℂ A (s ^ j)) P) ∧
    ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ev (fun j => m (q + j)) P

variable {L : LevelData A r} {Y : ℂ}

theorem Deg.mono {D E : ℕ} {Z : ℂ → A} (h : Deg L Y D Z) (hDE : D ≤ E) : Deg L Y E Z := by
  obtain ⟨P, h1, h2⟩ := h
  exact ⟨P, h1.trans hDE, h2⟩

theorem Deg.add {D : ℕ} {Z W : ℂ → A} (h : Deg L Y D Z) (h' : Deg L Y D W) :
    Deg L Y D (fun y => Z y + W y) := by
  obtain ⟨P, h1, h2, h3⟩ := h
  obtain ⟨Q, k1, k2, k3⟩ := h'
  refine ⟨P + Q, (natDegree_add_le _ _).trans (max_le h1 k1), fun s => ?_, fun m hm q => ?_⟩
  · rw [ev_add, ← h2, ← k2]
  · rw [ev_add, ← h3 m hm, ← k3 m hm, add_mul]

theorem Deg.mul {D E : ℕ} {Z W : ℂ → A} (h : Deg L Y D Z) (h' : Deg L Y E W) :
    Deg L Y (D + E) (fun y => Z y * W y) := by
  obtain ⟨P, h1, h2, h3⟩ := h
  obtain ⟨Q, k1, k2, k3⟩ := h'
  refine ⟨P * Q, natDegree_mul_le.trans (add_le_add h1 k1), fun s => ?_, fun m hm q => ?_⟩
  · show Z (Y + s) * W (Y + s) = _
    rw [k2]
    refine ev_mul _ _ _ _ _ fun j => ?_
    rw [← Algebra.commutes, h2, mul_ev]
    simp only [pow_add, map_mul]
  · show Z Y * W Y * m q = _
    rw [mul_assoc, k3 m hm]
    refine ev_mul _ _ _ _ _ fun j => ?_
    rw [h3 m hm]
    simp only [add_assoc]

theorem deg_const (a : A) (ha : ∀ m : ℕ → A, MulRel L m → ∀ q, a * m q = m q * a) :
    Deg L Y 0 (fun _ => a) := by
  refine ⟨monomial 0 a, natDegree_monomial_le _, fun s => ?_, fun m hm q => ?_⟩
  · rw [ev_monomial]; simp
  · rw [ev_monomial, ha m hm]; rfl

theorem deg_fn {a : A} (ha : a ∈ L.fns) : Deg L Y 0 (fun _ => a) :=
  deg_const a fun _ hm q => ((hm q).1 a ha).eq

theorem deg_lin (Z : ℂ → A) (b : A) (h1 : ∀ s, Z (Y + s) = Z Y + algebraMap ℂ A s * b)
    (h2 : ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = m q * Z Y + m (q + 1) * b) : Deg L Y 1 Z := by
  refine ⟨monomial 0 (Z Y) + monomial 1 b, (natDegree_add_le _ _).trans
    (max_le ((natDegree_monomial_le _).trans zero_le_one) (natDegree_monomial_le _)), fun s => ?_,
    fun m hm q => ?_⟩
  · rw [ev_add, ev_monomial, ev_monomial, h1]; simp
  · rw [ev_add, ev_monomial, ev_monomial, h2 m hm]; rfl

theorem deg_list (l : List A) (hl : ∀ a ∈ l, a ∈ L.fns) : Deg L Y 0 (fun _ => l.prod) := by
  induction l with
  | nil => exact deg_const _ (by simp)
  | cons a l ih =>
    simpa using (deg_fn (hl a (by simp))).mul (ih fun b hb => hl b (by simp [hb]))

theorem deg_Tl (l : Fin r) (i j : Fin 2) : Deg L Y 1 (fun y => L.Tl y l i j) := by
  have hc : L.c l ∈ L.fns := by simp [LevelData.fns]
  have hci : L.ci l ∈ L.fns := by simp [LevelData.fns]
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tl]
  · refine deg_lin _ 1 (fun s => ?_) fun m hm q => ?_
    · simp [add_right_comm]
    · simp [add_mul, mul_add, (hm q).2.1 l, Algebra.commutes, add_assoc]
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    exact ((hm q).1 _ hc).neg_left.eq
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    simpa using ((hm q).1 _ hci).eq
  · refine (deg_const _ fun m hm q => ?_).mono zero_le_one
    exact (Commute.zero_left (m q)).eq

theorem deg_prod (l : List (Fin r)) (i j : Fin 2) :
    Deg L Y l.length (fun y => (l.map (L.Tl y)).prod i j) := by
  induction l generalizing i j with
  | nil =>
    refine deg_const ((1 : Matrix (Fin 2) (Fin 2) A) i j) fun m _ q => ?_
    rw [Matrix.one_apply]; split_ifs <;> simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, List.length_cons]
    rw [add_comm l.length 1]
    exact ((deg_Tl a i 0).mul (ih 0 j)).add ((deg_Tl a i 1).mul (ih 1 j))

theorem deg_Tprod (i j : Fin 2) : Deg L Y r (fun y => L.Tprod y i j) := by
  have h := deg_prod (L := L) (Y := Y) (List.finRange r).reverse i j
  simp only [List.length_reverse, List.length_finRange] at h
  simpa only [LevelData.Tprod, List.ofFn_eq_map, List.map_reverse] using h

theorem forwardTaylorDegree_one_leftLetter : Deg L Y 1 L.l0 := by
  refine deg_lin _ (-(L.ζb * L.GGi)) (fun s => ?_) fun m hm q => ?_
  · simp only [LevelData.l0, add_right_comm Y s, map_add (algebraMap ℂ A) (Y + 1 / 2) s]
    noncomm_ring
  · have c1 : ∀ q, Commute (L.ζb * L.GGi) (m q) := fun q =>
      ((hm q).1 _ (by simp [LevelData.fns])).mul_left ((hm q).1 _ (by simp [LevelData.fns]))
    have c2 : Commute (algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) (m q) :=
      (Algebra.commute_algebraMap_left _ _).mul_left (c1 q)
    rw [LevelData.l0, sub_mul, neg_mul, (hm q).2.2.2.1, c2.eq, (c1 (q + 1)).eq]
    noncomm_ring

theorem deg_Ahat : Deg L Y r L.Ahat := by
  have h := (deg_list (L := L) (Y := Y) (List.ofFn L.c) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    simp [LevelData.fns])).mul (deg_Tprod 0 0)
  rw [zero_add] at h
  exact h

theorem forwardTaylorDegree_plusHatR : Deg L Y (r + 1) L.R0 := by
  have h := ((deg_list (L := L) (Y := Y) (List.ofFn L.cb) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    simp [LevelData.fns])).mul (deg_fn (a := L.GG) (by simp [LevelData.fns]))).mul
    ((forwardTaylorDegree_one_leftLetter.mul (deg_Tprod 0 0)).add ((deg_Tprod 1 0).mono (Nat.le_add_left _ _)))
  rw [zero_add, zero_add, add_comm 1 r] at h
  exact h

theorem taylor_plus : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahat (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0 (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahat Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0 Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  intro A _ _ r L Y
  obtain ⟨P, h1, h2, h3⟩ := deg_Ahat (L := L) (Y := Y)
  obtain ⟨Q, k1, k2, k3⟩ := forwardTaylorDegree_plusHatR (L := L) (Y := Y)
  have hP : P.natDegree < r + 2 := by omega
  have hQ : Q.natDegree < r + 2 := by omega
  refine ⟨P.coeff, Q.coeff, fun s => ?_, fun s => ?_, fun m hm q => ⟨?_, ?_⟩⟩
  · rw [h2, ev_eq_sum _ _ _ hP]; simp only [Algebra.smul_def]
  · rw [k2, ev_eq_sum _ _ _ hQ]; simp only [Algebra.smul_def]
  · rw [h3 m hm, ev_eq_sum _ _ _ hP]
  · rw [k3 m hm, ev_eq_sum _ _ _ hQ]

end

end GlobalTheory.HatTaylorPlus
