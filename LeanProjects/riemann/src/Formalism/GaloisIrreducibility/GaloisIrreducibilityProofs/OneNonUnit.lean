import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility
open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

@[simp] lemma zero_ne_succ' {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := ⟨fun h => Fin.succ_ne_zero k h.symm, fun h => h.elim⟩

def bord {m : ℕ} (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m+1)) (Fin (m+1)) R :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (M i)))

@[simp] lemma bord_zero_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) R) : bord M 0 0 = 1 := by
  simp [bord]
@[simp] lemma bord_zero_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    bord M 0 j.succ = 0 := by
  simp [bord]
@[simp] lemma bord_succ_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    bord M i.succ 0 = 0 := by
  simp [bord]
@[simp] lemma bord_succ_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    bord M i.succ j.succ = M i j := by
  simp [bord]

lemma bord_mul {m : ℕ} (M N : Matrix (Fin m) (Fin m) R) : bord M * bord N = bord (M * N) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

lemma bord_one {m : ℕ} : bord (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply]

lemma bord_isUnit {m : ℕ} {M : Matrix (Fin m) (Fin m) R} (h : IsUnit M) : IsUnit (bord M) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨⟨bord (u : Matrix (Fin m) (Fin m) R), bord (↑u⁻¹ : Matrix (Fin m) (Fin m) R), ?_, ?_⟩, rfl⟩
  · first
    | rw [bord_mul, Units.mul_inv, bord_one]
    | simp [bord_mul, bord_one]
  · first
    | rw [bord_mul, Units.inv_mul, bord_one]
    | simp [bord_mul, bord_one]

lemma bord_diag {n : ℕ} (d : R) :
    bord (diagonal fun i : Fin (n+1) => if (i : ℕ) = n then d else 1) =
      diagonal fun i : Fin (n+2) => if (i : ℕ) = n + 1 then d else 1 := by
  have h0 : (0 : ℕ) ≠ n + 1 := by omega
  have h0' : n + 1 ≠ 0 := by omega
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.diagonal_apply, h0, h0']

lemma bord_map {S : Type} [CommRing S] (φ : R →+* S) {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    (bord M).map φ = bord (M.map φ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.map_apply]

lemma rank_add_le' {K : Type} [Field K] {m : ℕ} (A B : Matrix (Fin m) (Fin m) K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma rank_bord_le {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K) :
    (bord M).rank ≤ M.rank + 1 := by
  classical
  let S : Matrix (Fin (m+1)) (Fin m) K := Matrix.of fun i k => if i = k.succ then 1 else 0
  let T : Matrix (Fin m) (Fin (m+1)) K := Matrix.of fun k j => if j = k.succ then 1 else 0
  let S' : Matrix (Fin (m+1)) (Fin 1) K := Matrix.of fun i _ => if i = 0 then 1 else 0
  let T' : Matrix (Fin 1) (Fin (m+1)) K := Matrix.of fun _ j => if j = 0 then 1 else 0
  have hsplit : bord M = S' * T' + S * M * T := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [S, T, S', T', Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hsplit]
  refine (rank_add_le' _ _).trans ?_
  have h1 : (S' * T').rank ≤ 1 :=
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width S')
  have h2 : (S * M * T).rank ≤ M.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  omega

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

def Equi {s : ℕ} (A B : Matrix (Fin s) (Fin s) R) : Prop :=
  ∃ P Q : Matrix (Fin s) (Fin s) R, IsUnit P ∧ IsUnit Q ∧ P * A * Q = B

lemma Equi.trans {s : ℕ} {A B C : Matrix (Fin s) (Fin s) R} (h1 : Equi A B) (h2 : Equi B C) :
    Equi A C := by
  unfold Equi at h1 h2 ⊢
  obtain ⟨P1, Q1, hP1, hQ1, rfl⟩ := h1
  obtain ⟨P2, Q2, hP2, hQ2, rfl⟩ := h2
  exact ⟨P2 * P1, Q1 * Q2, hP2.mul hP1, hQ1.mul hQ2, by simp only [Matrix.mul_assoc]⟩

lemma Equi.rank_map {K : Type} [Field K] (φ : R →+* K) {s : ℕ}
    {A B : Matrix (Fin s) (Fin s) R} (h : Equi A B) : (B.map φ).rank = (A.map φ).rank := by
  unfold Equi at h
  obtain ⟨P, Q, hP, hQ, rfl⟩ := h
  have hP' : IsUnit (P.map φ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; simpa using hP.map φ.mapMatrix
  have hQ' : IsUnit (Q.map φ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; simpa using hQ.map φ.mapMatrix
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP']

lemma perm_isUnit {s : ℕ} (σ : Equiv.Perm (Fin s)) :
    IsUnit (σ.toPEquiv.toMatrix : Matrix (Fin s) (Fin s) R) := by
  refine ⟨⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, ?_, ?_⟩, rfl⟩
  · first
    | rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
    | simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  · first
    | rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
    | simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]

lemma equi_submatrix {s : ℕ} (A : Matrix (Fin s) (Fin s) R) (σ τ : Equiv.Perm (Fin s)) :
    Equi A (A.submatrix σ τ) := by
  unfold Equi
  refine ⟨σ.toPEquiv.toMatrix, τ.symm.toPEquiv.toMatrix, perm_isUnit σ, perm_isUnit τ.symm, ?_⟩
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp

lemma clear {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (hu : IsUnit (A 0 0)) :
    ∃ A' : Matrix (Fin m) (Fin m) R, Equi A (bord A') := by
  obtain ⟨b, hb⟩ : ∃ b : R, A 0 0 * b = 1 := ⟨_, hu.mul_val_inv⟩
  have hb' : b * A 0 0 = 1 := by rw [mul_comm]; exact hb
  set P : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons 1 0)
    (fun i => Fin.cons (-(A i.succ 0 * b)) (fun j => if i = j then 1 else 0))) with hP
  set Pinv : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons 1 0)
    (fun i => Fin.cons (A i.succ 0 * b) (fun j => if i = j then 1 else 0))) with hPinv
  set Q : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons b (fun j => -(b * A 0 j.succ)))
    (fun i => Fin.cons 0 (fun j => if i = j then 1 else 0))) with hQ
  set Qinv : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons (A 0 0) (fun j => A 0 j.succ))
    (fun i => Fin.cons 0 (fun j => if i = j then 1 else 0))) with hQinv
  set A' : Matrix (Fin m) (Fin m) R := Matrix.of fun i j => A i.succ j.succ - A i.succ 0 * b * A 0 j.succ
    with hA'
  have hPP : P * Pinv = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [hP, hPinv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hQQ : Q * Qinv = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [hQ, hQinv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hb']
  have hPu : IsUnit P := by
    have h : P.det * Pinv.det = 1 := by rw [← Matrix.det_mul, hPP, Matrix.det_one]
    rw [Matrix.isUnit_iff_isUnit_det]
    first
    | exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
    | exact IsUnit.of_mul_eq_one _ h
  have hQu : IsUnit Q := by
    have h : Q.det * Qinv.det = 1 := by rw [← Matrix.det_mul, hQQ, Matrix.det_one]
    rw [Matrix.isUnit_iff_isUnit_det]
    first
    | exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
    | exact IsUnit.of_mul_eq_one _ h
  have key : P * A * Q = bord A' := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination hb | linear_combination (-1 : R) * hb
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination (-(A 0 j.succ)) * hb | linear_combination (A 0 j.succ) * hb
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination (-(A i.succ 0 * b)) * hb' | linear_combination (A i.succ 0 * b) * hb'
    · simp [hP, hQ, hA', Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first
        | linear_combination (A i.succ 0 * b * A 0 j.succ) * hb'
        | linear_combination (-(A i.succ 0 * b * A 0 j.succ)) * hb'
  refine ⟨A', ?_⟩
  unfold Equi
  exact ⟨P, Q, hPu, hQu, key⟩

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R] [IsLocalRing R]

lemma main (n : ℕ) : ∀ (A : Matrix (Fin (n+1)) (Fin (n+1)) R),
    n ≤ (A.map (IsLocalRing.residue R)).rank →
    ∃ d : R, Equi A (diagonal fun i : Fin (n+1) => if (i : ℕ) = n then d else 1) := by
  induction n with
  | zero =>
    intro A _
    refine ⟨A 0 0, ?_⟩
    unfold Equi
    refine ⟨1, 1, isUnit_one, isUnit_one, ?_⟩
    ext i j
    fin_cases i; fin_cases j
    simp
  | succ n ih =>
    intro A hA
    obtain ⟨i, j, hij⟩ : ∃ i j, IsUnit (A i j) := by
      by_contra hne
      push_neg at hne
      have h0 : A.map (IsLocalRing.residue R) = 0 := by
        ext i j
        simp only [Matrix.map_apply, Matrix.zero_apply]
        exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (hne i j))
      rw [h0, Matrix.rank_zero] at hA
      omega
    have hu : IsUnit ((A.submatrix (Equiv.swap 0 i) (Equiv.swap 0 j)) 0 0) := by
      simpa using hij
    obtain ⟨A', e2⟩ := clear _ hu
    have e12 : Equi A (bord A') := (equi_submatrix A _ _).trans e2
    have hr : n ≤ (A'.map (IsLocalRing.residue R)).rank := by
      have h1 := e12.rank_map (IsLocalRing.residue R)
      have h2 := rank_bord_le (A'.map (IsLocalRing.residue R))
      rw [← bord_map, h1] at h2
      omega
    obtain ⟨d, hd⟩ := ih A' hr
    unfold Equi at hd
    obtain ⟨P, Q, hP, hQ, hPQ⟩ := hd
    refine ⟨d, e12.trans ?_⟩
    unfold Equi
    refine ⟨bord P, bord Q, bord_isUnit hP, bord_isUnit hQ, ?_⟩
    rw [bord_mul, bord_mul, hPQ, bord_diag]

end BorderedIndexCases

end Formalism.GaloisIrreducibility
