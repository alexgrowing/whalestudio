import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.CellBase

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW.CellW

open NumberField Formalism.MainNotions.S Matrix

variable {E : Type} [Field E] [NumberField E]

def revJ (K : Type*) [Zero K] [One K] (s : ℕ) : Matrix (Fin s) (Fin s) K :=
  fun i j => if j = Fin.rev i then 1 else 0

section Rev

variable {K : Type*} [Field K] {s : ℕ}

theorem revJ_mul_apply (M : Matrix (Fin s) (Fin s) K) (i j : Fin s) : (revJ K s * M) i j = M (Fin.rev i) j := by
  rw [mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [revJ]
  · intro k _ hk; simp [revJ, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_revJ_apply (M : Matrix (Fin s) (Fin s) K) (i j : Fin s) : (M * revJ K s) i j = M i (Fin.rev j) := by
  rw [mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [revJ]
  · intro k _ hk
    have : j ≠ Fin.rev k := by
      intro h; apply hk; rw [h, Fin.rev_rev]
    simp [revJ, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem revJ_revJ : revJ K s * revJ K s = 1 := by
  ext i j
  rw [revJ_mul_apply]
  simp only [revJ, Fin.rev_rev, one_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem revJ_conj_up {L : Matrix (Fin s) (Fin s) K} (hL : IsLoUni L) : IsUpUni (revJ K s * L * revJ K s) := by
  intro i j
  rw [mul_revJ_apply, revJ_mul_apply]
  refine ⟨fun h => (hL _ _).1 (Fin.rev_lt_rev.mpr h), fun h => (hL _ _).2 (by rw [h])⟩

end Rev

theorem intg_revJ (x : E) (m o : 𝓞 E) (h : algebraMap (𝓞 E) E o = algebraMap (𝓞 E) E m * x) (s : ℕ) :
    Intg m (x • revJ E s) := by
  refine ⟨o • revJ (𝓞 E) s, ?_⟩
  ext i j
  by_cases hij : j = Fin.rev i <;> simp [revJ, hij, h]

section Blocks

variable {K : Type*} {s n : ℕ}

theorem blocks_eq (M : Matrix (Fin (s + n)) (Fin (s + n)) K) :
    M.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (M.submatrix (Fin.castAdd n) (Fin.castAdd n)) (M.submatrix (Fin.castAdd n) (Fin.natAdd s))
        (M.submatrix (Fin.natAdd s) (Fin.castAdd n)) (M.submatrix (Fin.natAdd s) (Fin.natAdd s)) := by
  ext (i | i) (j | j) <;> simp

variable [CommRing K]

theorem lo_11 {L : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsLoUni L) :
    IsLoUni (L.submatrix (Fin.castAdd n) (Fin.castAdd n)) := by
  intro i j
  refine ⟨fun hij => (h _ _).1 ?_, fun hij => (h _ _).2 (by rw [hij])⟩
  rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_castAdd]; exact hij

theorem lo_22 {L : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsLoUni L) :
    IsLoUni (L.submatrix (Fin.natAdd s) (Fin.natAdd s)) := by
  intro i j
  refine ⟨fun hij => (h _ _).1 ?_, fun hij => (h _ _).2 (by rw [hij])⟩
  rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_natAdd]; omega

theorem lo_12 {L : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsLoUni L) :
    L.submatrix (Fin.castAdd n) (Fin.natAdd s) = 0 := by
  ext i j
  refine (h _ _).1 ?_
  rw [Fin.lt_def]; simp only [Fin.val_castAdd, Fin.val_natAdd]; have := i.isLt; omega

theorem up_11 {U : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsUpUni U) :
    IsUpUni (U.submatrix (Fin.castAdd n) (Fin.castAdd n)) := by
  intro i j
  refine ⟨fun hij => (h _ _).1 ?_, fun hij => (h _ _).2 (by rw [hij])⟩
  rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_castAdd]; exact hij

theorem up_22 {U : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsUpUni U) :
    IsUpUni (U.submatrix (Fin.natAdd s) (Fin.natAdd s)) := by
  intro i j
  refine ⟨fun hij => (h _ _).1 ?_, fun hij => (h _ _).2 (by rw [hij])⟩
  rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_natAdd]; omega

theorem up_21 {U : Matrix (Fin (s + n)) (Fin (s + n)) K} (h : IsUpUni U) :
    U.submatrix (Fin.natAdd s) (Fin.castAdd n) = 0 := by
  ext i j
  refine (h _ _).1 ?_
  rw [Fin.lt_def]; simp only [Fin.val_castAdd, Fin.val_natAdd]; have := j.isLt; omega

theorem cast_lt_cast {i j : Fin s} : Fin.castAdd n i < Fin.castAdd n j ↔ i < j := by
  rw [Fin.lt_def, Fin.lt_def]; simp only [Fin.val_castAdd]

theorem nat_lt_nat {i j : Fin n} : Fin.natAdd s i < Fin.natAdd s j ↔ i < j := by
  rw [Fin.lt_def, Fin.lt_def]; simp only [Fin.val_natAdd]; omega

theorem cast_ne_nat (i : Fin s) (j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd s j := by
  intro h; have h1 := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
  have := i.isLt; omega

theorem not_nat_lt_cast (i : Fin n) (j : Fin s) : ¬ Fin.natAdd s i < Fin.castAdd n j := by
  rw [Fin.lt_def]; simp only [Fin.val_castAdd, Fin.val_natAdd]; have := j.isLt; omega

theorem lo_of_blocks {A : Matrix (Fin s) (Fin s) K} {C : Matrix (Fin n) (Fin s) K}
    {D : Matrix (Fin n) (Fin n) K} (hA : IsLoUni A) (hD : IsLoUni D) :
    IsLoUni ((fromBlocks A 0 C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) := by
  intro i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁, cast_lt_cast,
        Fin.castAdd_inj]
      exact hA i j
    | right j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        fromBlocks_apply₁₂, Matrix.zero_apply]
      exact ⟨by simp, fun h => absurd h (cast_ne_nat i j)⟩
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        fromBlocks_apply₂₁]
      exact ⟨fun h => absurd h (not_nat_lt_cast i j), fun h => absurd h.symm (cast_ne_nat j i)⟩
    | right j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂, nat_lt_nat,
        Fin.natAdd_inj]
      exact hD i j

theorem up_of_blocks {A : Matrix (Fin s) (Fin s) K} {B : Matrix (Fin s) (Fin n) K}
    {D : Matrix (Fin n) (Fin n) K} (hA : IsUpUni A) (hD : IsUpUni D) :
    IsUpUni ((fromBlocks A B 0 D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) := by
  intro i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁, cast_lt_cast,
        Fin.castAdd_inj]
      exact hA i j
    | right j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        fromBlocks_apply₁₂]
      exact ⟨fun h => absurd h (not_nat_lt_cast j i), fun h => absurd h (cast_ne_nat i j)⟩
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        fromBlocks_apply₂₁, Matrix.zero_apply]
      exact ⟨by simp, fun h => absurd h.symm (cast_ne_nat j i)⟩
    | right j =>
      simp only [submatrix_apply, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂, nat_lt_nat,
        Fin.natAdd_inj]
      exact hD i j

end Blocks

theorem lo_one {K : Type*} [Field K] {k : ℕ} : IsLoUni (1 : Matrix (Fin k) (Fin k) K) := by
  intro i j
  exact ⟨fun h => one_apply_ne (ne_of_lt h), fun h => by rw [h, one_apply_eq]⟩

def BDm {N : ℕ} (W : Matrix (Fin N) (Fin N) E) : Prop :=
  ∀ d : 𝓞 E, d ≠ 0 → ∃ D : 𝓞 E, D ≠ 0 ∧ ∀ Z : Matrix (Fin N) (Fin N) E, Intg d Z →
    (∃ L0 U0, IsLoUni L0 ∧ IsUpUni U0 ∧ Z = L0 * W * U0) →
    ∃ L1 U1, IsLoUni L1 ∧ IsUpUni U1 ∧ Z = L1 * W * U1 ∧ Intg D L1 ∧ Intg D U1

theorem submatrix_equiv_prod {K : Type*} [CommRing K] {m n : Type*} [Fintype m] [Fintype n]
    (e : m ≃ n) (A B C : Matrix n n K) :
    (A * B * C).submatrix e e = A.submatrix e e * B.submatrix e e * C.submatrix e e := by
  rw [submatrix_mul_equiv, submatrix_mul_equiv]

theorem bd_step {s n : ℕ} (t : E) (ht : t ≠ 0) (W' : Matrix (Fin n) (Fin n) E)
    (W : Matrix (Fin (s + n)) (Fin (s + n)) E)
    (hW : W.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks (t • revJ E s) 0 0 W')
    (ih : BDm W') : BDm W := by
  intro d hd
  obtain ⟨mt, hmt, ot, hot⟩ := exists_den t⁻¹
  have hD1 : mt * d ≠ 0 := mul_ne_zero hmt hd
  have hδ : (mt * d) ^ (s - 1) * mt ≠ 0 := mul_ne_zero (pow_ne_zero _ hD1) hmt
  have hd' : d * ((mt * d) ^ (s - 1) * mt) * d ≠ 0 := mul_ne_zero (mul_ne_zero hd hδ) hd
  obtain ⟨D', hD', hih⟩ := ih _ hd'
  refine ⟨d * ((mt * d) ^ (s - 1) * mt) * (mt * d) * D', mul_ne_zero (mul_ne_zero (mul_ne_zero hd hδ) hD1) hD', ?_⟩
  rintro Z hZ ⟨L0, U0, hL0, hU0, hZe⟩

  set P := Z.submatrix (Fin.castAdd n) (Fin.castAdd n) with hPdef
  set Q := Z.submatrix (Fin.castAdd n) (Fin.natAdd s) with hQdef
  set R := Z.submatrix (Fin.natAdd s) (Fin.castAdd n) with hRdef
  set S := Z.submatrix (Fin.natAdd s) (Fin.natAdd s) with hSdef
  set liftZP_unit := L0.submatrix (Fin.castAdd n) (Fin.castAdd n)
  set lintegral_supP_lt_top₂ := L0.submatrix (Fin.natAdd s) (Fin.castAdd n)
  set lix_inf_of_locP_le := L0.submatrix (Fin.natAdd s) (Fin.natAdd s)
  set U11 := U0.submatrix (Fin.castAdd n) (Fin.castAdd n)
  set U12 := U0.submatrix (Fin.castAdd n) (Fin.natAdd s)
  set U22 := U0.submatrix (Fin.natAdd s) (Fin.natAdd s)
  set W1 := t • revJ E s with hW1
  set W1i := t⁻¹ • revJ E s with hW1i
  have hW1W1i : W1 * W1i = 1 := by
    rw [hW1, hW1i, smul_mul_smul_comm, mul_inv_cancel₀ ht, one_smul, revJ_revJ]
  have hW1iW1 : W1i * W1 = 1 := by
    rw [hW1, hW1i, smul_mul_smul_comm, inv_mul_cancel₀ ht, one_smul, revJ_revJ]
  have key : Z.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (liftZP_unit * W1 * U11) (liftZP_unit * W1 * U12) (lintegral_supP_lt_top₂ * W1 * U11) (lintegral_supP_lt_top₂ * W1 * U12 + lix_inf_of_locP_le * W' * U22) := by
    rw [hZe, submatrix_equiv_prod, hW, blocks_eq L0, blocks_eq U0, lo_12 hL0, up_21 hU0,
      fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_assoc]
    rfl
  rw [blocks_eq Z, fromBlocks_inj] at key
  obtain ⟨hP0, hQ0, hR0, hS0⟩ := key
  have hP : P = liftZP_unit * W1 * U11 := hP0
  have hQ : Q = liftZP_unit * W1 * U12 := hQ0
  have hR : R = lintegral_supP_lt_top₂ * W1 * U11 := hR0
  have hS : S = lintegral_supP_lt_top₂ * W1 * U12 + lix_inf_of_locP_le * W' * U22 := hS0

  set U1 := W1i * P with hU1def
  have hU1 : IsUpUni U1 := by
    have : U1 = (revJ E s * liftZP_unit * revJ E s) * U11 := by
      rw [hU1def, hP, hW1i, hW1]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ht, mul_inv_cancel₀ ht, one_smul,
        Matrix.mul_assoc]
    rw [this]
    exact up_mul (revJ_conj_up (lo_11 hL0)) (up_11 hU0)
  have hWU1 : W1 * U1 = P := by rw [hU1def, ← Matrix.mul_assoc, hW1W1i, Matrix.one_mul]
  set Pinv := U1.adjugate * W1i with hPinvdef
  have hPinvP : Pinv * P = 1 := by
    rw [hPinvdef, ← hWU1, Matrix.mul_assoc, ← Matrix.mul_assoc W1i, hW1iW1, Matrix.one_mul, up_adj_mul hU1]
  have hPPinv : P * Pinv = 1 := mul_eq_one_comm.mp hPinvP
  have hX : (W1 * U11 * Pinv) * liftZP_unit = 1 := by
    apply mul_eq_one_comm.mp
    rw [show liftZP_unit * (W1 * U11 * Pinv) = P * Pinv by rw [hP]; simp only [Matrix.mul_assoc], hPPinv]
  have hRPQ : R * Pinv * Q = lintegral_supP_lt_top₂ * W1 * U12 := by
    rw [hR, hQ]
    calc lintegral_supP_lt_top₂ * W1 * U11 * Pinv * (liftZP_unit * W1 * U12) = lintegral_supP_lt_top₂ * ((W1 * U11 * Pinv) * liftZP_unit) * W1 * U12 := by
          simp only [Matrix.mul_assoc]
      _ = lintegral_supP_lt_top₂ * W1 * U12 := by rw [hX, Matrix.mul_one]
  have hS' : S - R * Pinv * Q = lix_inf_of_locP_le * W' * U22 := by rw [hRPQ, hS]; abel

  have hPi : Intg d P := intg_submatrix hZ _ _
  have hQi : Intg d Q := intg_submatrix hZ _ _
  have hRi : Intg d R := intg_submatrix hZ _ _
  have hSi : Intg d S := intg_submatrix hZ _ _
  have hW1ii : Intg mt W1i := intg_revJ _ _ _ hot s
  have hU1i : Intg (mt * d) U1 := intg_mul hW1ii hPi
  have hPinvi : Intg ((mt * d) ^ (s - 1) * mt) Pinv := by
    exact intg_mul (intg_adj hU1i) hW1ii
  have hRPi : Intg (d * ((mt * d) ^ (s - 1) * mt)) (R * Pinv) := intg_mul hRi hPinvi
  have hS'i : Intg (d * ((mt * d) ^ (s - 1) * mt) * d) (S - R * Pinv * Q) :=
    intg_sub (intg_dvd hSi ⟨(mt * d) ^ (s - 1) * mt * d, by ring⟩) (intg_mul hRPi hQi)
  obtain ⟨L2, U2, hL2, hU2, hS2, hL2i, hU2i⟩ :=
    hih _ hS'i ⟨lix_inf_of_locP_le, U22, lo_22 hL0, up_22 hU0, hS'⟩

  refine ⟨(fromBlocks 1 0 (R * Pinv) L2).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    (fromBlocks U1 (W1i * Q) 0 U2).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    lo_of_blocks (lo_one (K := E)) hL2, up_of_blocks hU1 hU2, ?_, ?_, ?_⟩
  · have hZZ : Z = (Z.submatrix finSumFinEquiv finSumFinEquiv).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      simp
    have hWW : W = (W.submatrix finSumFinEquiv finSumFinEquiv).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      simp
    rw [hWW, ← submatrix_equiv_prod, hW, fromBlocks_multiply, fromBlocks_multiply, hZZ, blocks_eq Z]
    congr 1
    have hc : ∀ {m : ℕ} (X : Matrix (Fin s) (Fin m) E), W1 * (W1i * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hW1W1i, Matrix.one_mul]
    have h22 := sub_eq_iff_eq_add'.mp hS2
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_assoc, hU1def,
      hc] at h22 ⊢
    rw [fromBlocks_inj]
    refine ⟨rfl, rfl, ?_, h22⟩
    rw [hPinvP, Matrix.mul_one]
  · refine intg_submatrix (intg_fromBlocks (intg_one _) (intg_zero _) (intg_dvd hRPi ?_) (intg_dvd hL2i ?_)) _ _
    · exact ⟨(mt * d) * D', by ring⟩
    · exact ⟨d * ((mt * d) ^ (s - 1) * mt) * (mt * d), by ring⟩
  · refine intg_submatrix (intg_fromBlocks (intg_dvd hU1i ?_) (intg_dvd (intg_mul hW1ii hQi) ?_) (intg_zero _)
      (intg_dvd hU2i ?_)) _ _
    · exact ⟨d * ((mt * d) ^ (s - 1) * mt) * D', by ring⟩
    · exact ⟨d * ((mt * d) ^ (s - 1) * mt) * D', by ring⟩
    · exact ⟨d * ((mt * d) ^ (s - 1) * mt) * (mt * d), by ring⟩

end PI.TermsAtPtFiniteW.CellW
