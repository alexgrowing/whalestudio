import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl

namespace GlobalTheory.FrameCompletion

section Basic

variable {L : Type} [Field L] {σ : L →+* L}

theorem conjT_add {m p : Type} (A B : Matrix m p L) : cT σ (A + B) = cT σ A + cT σ B := by
  ext i j; simp [cT]

theorem conjT_sub {m p : Type} (A B : Matrix m p L) : cT σ (A - B) = cT σ A - cT σ B := by
  ext i j; simp [cT]

theorem conjT_neg {m p : Type} (A : Matrix m p L) : cT σ (-A) = -cT σ A := by
  ext i j; simp [cT]

theorem conjT_smul {m p : Type} (c : L) (A : Matrix m p L) : cT σ (c • A) = σ c • cT σ A := by
  ext i j; simp [cT]

theorem conjT_zero {m p : Type} : cT σ (0 : Matrix m p L) = 0 := by
  ext i j; simp [cT]

theorem conjT_conjT (hσσ : ∀ x, σ (σ x) = x) {m p : Type} (A : Matrix m p L) : cT σ (cT σ A) = A := by
  ext i j; simp [cT, hσσ]

theorem conjT_fromRows {m m' p : Type} (A : Matrix m p L) (B : Matrix m' p L) :
    cT σ (fromRows A B) = fromCols (cT σ A) (cT σ B) := by
  ext i (j | j) <;> simp [cT]

theorem conjT_fromCols {m p p' : Type} (A : Matrix m p L) (B : Matrix m p' L) :
    cT σ (fromCols A B) = fromRows (cT σ A) (cT σ B) := by
  ext (i | i) j <;> simp [cT]

theorem conjT_fromBlocks {m m' p p' : Type} (A : Matrix m p L) (B : Matrix m p' L) (C : Matrix m' p L)
    (D : Matrix m' p' L) : cT σ (fromBlocks A B C D) = fromBlocks (cT σ A) (cT σ C) (cT σ B) (cT σ D) := by
  ext (i | i) (j | j) <;> simp [cT]

theorem conjT_antiJ {n : ℕ} : cT σ (antiJ L n) = antiJ L n := by
  ext i j
  simp only [cT, antiJ, Matrix.transpose_apply, Matrix.map_apply]
  rw [add_comm j.val i.val]
  split_ifs <;> simp

theorem antiJ_mul_antiJ_mul [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {p : Type} (X : Matrix (Fin n) p L) : antiJ L n * (antiJ L n * X) = X := by
  rw [← Matrix.mul_assoc, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]

def gramQ (L : Type) [Field L] (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L :=
  fromBlocks (antiJ L n) 0 0 (-antiJ L n)

theorem conjT_gramQ {n : ℕ} : cT σ (gramQ L n) = gramQ L n := by
  rw [gramQ, conjT_fromBlocks, conjT_antiJ, conjT_zero, conjT_neg, conjT_antiJ]

theorem pair_symm (hσσ : ∀ x, σ (σ x) = x) {n : ℕ} {κ μ : Type} (X : Matrix (Fin n ⊕ Fin n) κ L)
    (X' : Matrix (Fin n ⊕ Fin n) μ L) : cT σ (cT σ X * gramQ L n * X') = cT σ X' * gramQ L n * X := by
  simp only [cT_mul, conjT_conjT hσσ, conjT_gramQ, Matrix.mul_assoc]

theorem pair_fromRows {n : ℕ} {κ μ : Type} (C D : Matrix (Fin n) κ L) (C' D' : Matrix (Fin n) μ L) :
    cT σ (fromRows C D) * gramQ L n * fromRows C' D' =
      cT σ C * antiJ L n * C' - cT σ D * antiJ L n * D' := by
  rw [conjT_fromRows, gramQ, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp [Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]

theorem pair_comb {ι κ : Type} [Fintype ι] [Fintype κ] (Q : Matrix ι ι L) (X W : Matrix ι κ L) (s t s' t' : L) :
    cT σ (s • X + t • W) * Q * (s' • X + t' • W) =
      (σ s * s') • (cT σ X * Q * X) + (σ s * t') • (cT σ X * Q * W) + (σ t * s') • (cT σ W * Q * X) +
        (σ t * t') • (cT σ W * Q * W) := by
  simp only [conjT_add, conjT_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc]
  module

theorem pair_sub {ι κ : Type} [Fintype ι] [Fintype κ] (Q : Matrix ι ι L) (X W : Matrix ι κ L) (M : Matrix κ κ L)
    (c : L) : cT σ (X - c • (W * M)) * Q * (X - c • (W * M)) =
      cT σ X * Q * X - c • (cT σ X * Q * W * M) - σ c • (cT σ M * (cT σ W * Q * X)) +
        (σ c * c) • (cT σ M * (cT σ W * Q * W) * M) := by
  simp only [conjT_sub, conjT_smul, cT_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc]
  module

end Basic

section Int

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem isInt_smul {ι κ : Type} {c : L} {M : Matrix ι κ L} (hc : c ∈ intL L) (hM : IsInt M) : IsInt (c • M) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)

theorem isInt_neg {ι κ : Type} {M : Matrix ι κ L} (hM : IsInt M) : IsInt (-M) := fun i j => neg_mem (hM i j)

theorem isInt_sub {ι κ : Type} {M N : Matrix ι κ L} (hM : IsInt M) (hN : IsInt N) : IsInt (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem isInt_conjT (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {ι κ : Type} {M : Matrix ι κ L} (hM : IsInt M) :
    IsInt (cT σ M) := fun i j => by
  show Valued.v (σ (M j i)) ≤ 1
  rw [hσ]
  exact hM j i

theorem isInt_fromRows {ι ι' κ : Type} {A : Matrix ι κ L} {B : Matrix ι' κ L} (hA : IsInt A) (hB : IsInt B) :
    IsInt (fromRows A B) := by
  rintro (i | i) j
  exacts [hA i j, hB i j]

theorem isInt_fromCols {ι κ κ' : Type} {A : Matrix ι κ L} {B : Matrix ι κ' L} (hA : IsInt A) (hB : IsInt B) :
    IsInt (fromCols A B) := by
  rintro i (j | j)
  exacts [hA i j, hB i j]

theorem isInt_submatrix {ι κ ι' κ' : Type} {M : Matrix ι κ L} (hM : IsInt M) (f : ι' → ι) (g : κ' → κ) :
    IsInt (M.submatrix f g) := fun i j => hM (f i) (g j)

theorem isInt_antiJ {n : ℕ} : IsInt (antiJ L n) := fun i j => by
  unfold antiJ
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem isInt_gramQ {n : ℕ} : IsInt (gramQ L n) := by
  rintro (i | i) (j | j)
  · exact isInt_antiJ i j
  · exact zero_mem _
  · exact zero_mem _
  · exact isInt_neg isInt_antiJ i j

end Int

section Main

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem exists_frame (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {τ : L} (hτ : τ ∈ intL L)
    (hτ1 : τ + σ τ = 1) (g U V C : Matrix (Fin n) (Fin n) L) (hg : cT σ g * antiJ L n * g = antiJ L n)
    (hUi : IsInt U) (hVi : IsInt V) (hCi : IsInt C) (hDi : IsInt (g * C)) (h5 : (U + V * g) * C = 1) :
    ∃ K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, IsInt K ∧ cT σ K * gramQ L n * K = gramQ L n ∧
      ∀ x : Fin n → L, K *ᵥ Sum.elim x x = Sum.elim (C *ᵥ x) ((g * C) *ᵥ x) := by
  set Q := gramQ L n with hQ
  set Y : Matrix (Fin n ⊕ Fin n) (Fin n) L := fromRows C (g * C) with hY
  set Z : Matrix (Fin n ⊕ Fin n) (Fin n) L := fromRows (antiJ L n * cT σ U * antiJ L n) (-(antiJ L n * cT σ V * antiJ L n)) with hZ
  have hYY : cT σ Y * Q * Y = 0 := by
    rw [hY, hQ, pair_fromRows, cT_mul,
      show cT σ C * cT σ g * antiJ L n * (g * C) = cT σ C * (cT σ g * antiJ L n * g) * C by simp only [Matrix.mul_assoc], hg, sub_self]
  have hUC : cT σ C * cT σ U + cT σ (g * C) * cT σ V = 1 := by
    rw [← cT_mul, ← cT_mul, ← conjT_add, ← Matrix.mul_assoc V, ← Matrix.add_mul, h5, cT_one]
  have hYZ : cT σ Y * Q * Z = antiJ L n := by
    rw [hY, hZ, hQ, pair_fromRows]
    calc _ = (cT σ C * cT σ U + cT σ (g * C) * cT σ V) * antiJ L n := by
          simp only [Matrix.mul_neg, sub_neg_eq_add, Matrix.add_mul, Matrix.mul_assoc, antiJ_mul_antiJ_mul]
      _ = antiJ L n := by rw [hUC, Matrix.one_mul]
  have hZY : cT σ Z * Q * Y = antiJ L n := by rw [← pair_symm hσσ, hYZ, conjT_antiJ]
  set H := cT σ Z * Q * Z with hH
  have hHH : cT σ H = H := pair_symm hσσ Z Z
  set Z' := Z - τ • (Y * (antiJ L n * H)) with hZ'
  have hYZ' : cT σ Y * Q * Z' = antiJ L n := by
    rw [hZ', Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hYY, Matrix.zero_mul, smul_zero, sub_zero, hYZ]
  have hZ'Y : cT σ Z' * Q * Y = antiJ L n := by rw [← pair_symm hσσ, hYZ', conjT_antiJ]
  have hZ'Z' : cT σ Z' * Q * Z' = 0 := by
    rw [hZ', pair_sub, hYY, hZY, hYZ, ← hH, cT_mul, hHH, conjT_antiJ, antiJ_mul_antiJ_mul, Matrix.mul_zero,
      Matrix.zero_mul, smul_zero, add_zero, Matrix.mul_assoc, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.mul_one,
      sub_sub, ← add_smul, hτ1, one_smul, sub_self]
  set a := τ • Y + (1 : L) • Z' with ha
  set b := σ τ • Y + (-1 : L) • Z' with hb
  have hInt : IsInt Y ∧ IsInt Z' := by
    have hYi : IsInt Y := isInt_fromRows hCi hDi
    refine ⟨hYi, isInt_sub (isInt_fromRows ?_ ?_) (isInt_smul hτ (hYi.mul (isInt_antiJ.mul ?_)))⟩
    · exact (isInt_antiJ.mul (isInt_conjT hσ hUi)).mul isInt_antiJ
    · exact isInt_neg ((isInt_antiJ.mul (isInt_conjT hσ hVi)).mul isInt_antiJ)
    · have hZi : IsInt Z := isInt_fromRows ((isInt_antiJ.mul (isInt_conjT hσ hUi)).mul isInt_antiJ)
        (isInt_neg ((isInt_antiJ.mul (isInt_conjT hσ hVi)).mul isInt_antiJ))
      exact ((isInt_conjT hσ hZi).mul isInt_gramQ).mul hZi
  have hστ : σ τ ∈ intL L := by
    show Valued.v (σ τ) ≤ 1
    rw [hσ]
    exact hτ
  refine ⟨fromCols a b, isInt_fromCols ?_ ?_, ?_, fun x => ?_⟩
  · exact (isInt_smul hτ hInt.1).add (isInt_smul (one_mem _) hInt.2)
  · exact (isInt_smul hστ hInt.1).add (isInt_smul (neg_mem (one_mem _)) hInt.2)
  · rw [conjT_fromCols, fromRows_mul, fromRows_mul_fromCols, ha, hb, pair_comb, pair_comb, pair_comb, pair_comb,
      hYY, hYZ', hZ'Y, hZ'Z', hQ, gramQ]
    simp only [smul_zero, add_zero, zero_add, map_one, map_neg, hσσ, mul_one, one_mul, mul_neg, neg_mul, neg_smul,
      neg_neg]
    rw [← add_smul, add_comm (σ τ), hτ1, one_smul, neg_add_cancel, add_neg_cancel, ← neg_add, ← add_smul, hτ1, one_smul]
  · rw [fromCols_mulVec_sumElim, ← Matrix.add_mulVec, ha, hb,
      show τ • Y + (1 : L) • Z' + (σ τ • Y + (-1 : L) • Z') = (τ + σ τ) • Y by module, hτ1, one_smul, hY,
      fromRows_mulVec]

end Main

theorem completion : Completion := by
  intro L _ _ ϖ σ q n hU g U V C hf
  obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
  obtain ⟨hUi, hVi, hCi, hDi, h5⟩ := hf
  obtain ⟨K, hKi, hKQ, hKx⟩ := exists_frame hU.1 hU.2.1 hτ hτ1 (mat g) U V C g.2 hUi hVi hCi hDi h5
  set e := finSumFinEquiv (m := n) (n := n) with he
  set k := K.submatrix e.symm e.symm with hk
  have hQs : GlobalTheory.Doubling.dblGram e (antiJ L n) = (gramQ L n).submatrix e.symm e.symm := rfl
  have hkQ : cT σ k * GlobalTheory.Doubling.dblGram e (antiJ L n) * k = GlobalTheory.Doubling.dblGram e (antiJ L n) := by
    rw [hQs, hk, show cT σ (K.submatrix e.symm e.symm) = (cT σ K).submatrix e.symm e.symm from rfl,
      submatrix_mul_equiv, submatrix_mul_equiv, hKQ]
  have hQQ : GlobalTheory.Doubling.dblGram e (antiJ L n) * GlobalTheory.Doubling.dblGram e (antiJ L n) = 1 := by
    rw [GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat_mul, neg_mul_neg, GlobalTheory.UnitarySwap.antiJ_mul_self,
      GlobalTheory.Doubling.blkMat_one]
  have hinv : GlobalTheory.Doubling.dblGram e (antiJ L n) * cT σ k * GlobalTheory.Doubling.dblGram e (antiJ L n) * k = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ k), hkQ, hQQ]
  have hQi : IsInt (GlobalTheory.Doubling.dblGram e (antiJ L n)) := by
    rw [hQs]
    exact isInt_submatrix isInt_gramQ _ _
  have hki : IsInt k := isInt_submatrix hKi _ _
  obtain ⟨W, hW, hWk⟩ := P.cartan_exists_glint (intL L) k _ (mul_eq_one_comm.1 hinv) hki
    ((hQi.mul (isInt_conjT hU.2.1 hki)).mul hQi)
  refine ⟨W, ?_, hW, fun x => ?_⟩
  · show cT σ (W : Matrix (Fin (n + n)) (Fin (n + n)) L) * _ * (W : Matrix (Fin (n + n)) (Fin (n + n)) L) = _
    rw [hWk, hkQ]
  · rw [hWk, hk, GlobalTheory.Doubling.pairVec, GlobalTheory.Doubling.pairVec, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id, hKx]

end GlobalTheory.FrameCompletion
