import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurEquiv

open Matrix

section Alg

variable {R : Type} [CommRing R]

def IsUT {n : ℕ} (U : Matrix (Fin n) (Fin n) R) : Prop := (∀ i j : Fin n, j < i → U i j = 0) ∧ ∀ i, U i i = 1

def sd {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : R := ∑ i : Fin n, ∑ j : Fin n, if j.val = i.val + 1 then M i j else 0

theorem superDiag_eq_sd {n : ℕ} (g : GL (Fin n) R) : GlobalTheory.Whittaker.superDiag g = sd (g : Matrix (Fin n) (Fin n) R) := by
  simp [GlobalTheory.Whittaker.superDiag, sd, Finset.sum_filter]

theorem det_of_isUT {n : ℕ} {U : Matrix (Fin n) (Fin n) R} (hU : IsUT U) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => hU.1 i j h)]
  simp [hU.2]

variable {m r : ℕ}

theorem eqv_symm_inl (i : Fin (m + 1)) : ((eqv m r).symm (Sum.inl i)).val = i.val := by simp [eqv]
theorem eqv_symm_inr (j : Fin (r + 1)) : ((eqv m r).symm (Sum.inr j)).val = m + 1 + j.val := by simp [eqv]

theorem blk_mul (M N : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : blk (M * N) = blk M * blk N :=
  (Matrix.submatrix_mul_equiv M N _ (eqv m r).symm _).symm

theorem blk_eq (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    blk M = fromBlocks (Aof M) (Bof M) (Cof M) (Dof M) := (fromBlocks_toBlocks _).symm

variable {U : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R}

theorem Cof_of_isUT (hU : IsUT U) : Cof U = 0 := by
  ext i j
  apply hU.1
  rw [Fin.lt_def, eqv_symm_inl, eqv_symm_inr]
  omega

theorem Aof_isUT (hU : IsUT U) : IsUT (Aof U) :=
  ⟨fun i j h => hU.1 _ _ (by rw [Fin.lt_def, eqv_symm_inl, eqv_symm_inl]; exact h), fun i => hU.2 _⟩

theorem Dof_isUT (hU : IsUT U) : IsUT (Dof U) :=
  ⟨fun i j h => hU.1 _ _ (by rw [Fin.lt_def, eqv_symm_inr, eqv_symm_inr]; rw [Fin.lt_def] at h; omega), fun i => hU.2 _⟩

variable (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R)

theorem blk_UM (hU : IsUT U) : blk (U * M) = fromBlocks (Aof U * Aof M + Bof U * Cof M) (Aof U * Bof M + Bof U * Dof M)
    (Dof U * Cof M) (Dof U * Dof M) := by
  rw [blk_mul, blk_eq U, blk_eq M, Cof_of_isUT hU, fromBlocks_multiply]
  simp

theorem Aof_mul (hU : IsUT U) : Aof (U * M) = Aof U * Aof M + Bof U * Cof M := by
  rw [Aof, blk_UM M hU, toBlocks_fromBlocks₁₁]
theorem Bof_mul (hU : IsUT U) : Bof (U * M) = Aof U * Bof M + Bof U * Dof M := by
  rw [Bof, blk_UM M hU, toBlocks_fromBlocks₁₂]
theorem Cof_mul (hU : IsUT U) : Cof (U * M) = Dof U * Cof M := by
  rw [Cof, blk_UM M hU, toBlocks_fromBlocks₂₁]
theorem Dof_mul (hU : IsUT U) : Dof (U * M) = Dof U * Dof M := by
  rw [Dof, blk_UM M hU, toBlocks_fromBlocks₂₂]

theorem isUnit_Dof_mul_iff (hU : IsUT U) : IsUnit (Dof (U * M)).det ↔ IsUnit (Dof M).det := by
  rw [Dof_mul M hU, det_mul, det_of_isUT (Dof_isUT hU), one_mul]

theorem Yof_mul (hU : IsUT U) : Yof (U * M) = Yof M := by
  have hu : IsUnit (Dof U).det := by rw [det_of_isUT (Dof_isUT hU)]; exact isUnit_one
  rw [Yof, Yof, Dof_mul M hU, Cof_mul M hU, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc (Dof U)⁻¹,
    nonsing_inv_mul _ hu, Matrix.one_mul]

theorem Scof_mul (hU : IsUT U) (hD : IsUnit (Dof M).det) : Scof (U * M) = Aof U * Scof M := by
  have hu : IsUnit (Dof U).det := by rw [det_of_isUT (Dof_isUT hU)]; exact isUnit_one
  have h1 : (Dof M)⁻¹ * (Dof U)⁻¹ * (Dof U * Cof M) = (Dof M)⁻¹ * Cof M := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Dof U)⁻¹, nonsing_inv_mul _ hu, Matrix.one_mul]
  rw [Scof, Scof, Aof_mul M hU, Bof_mul M hU, Dof_mul M hU, Cof_mul M hU, Matrix.mul_inv_rev, Matrix.mul_assoc _ _ (Dof U * Cof M), h1]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Dof M) (Dof M)⁻¹ (Cof M), mul_nonsing_inv _ hD, Matrix.one_mul]
  abel

theorem Xof_mul (hU : IsUT U) (hD : IsUnit (Dof M).det) :
    Xof (U * M) = Aof U * Xof M * (Dof U)⁻¹ + Bof U * (Dof U)⁻¹ := by
  rw [Xof, Xof, Bof_mul M hU, Dof_mul M hU, Matrix.mul_inv_rev]
  simp only [Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Dof M) (Dof M)⁻¹ (Dof U)⁻¹, mul_nonsing_inv _ hD, Matrix.one_mul]

theorem inv_first_column_of_upper_triangular {n : ℕ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hV : IsUT V) (l : Fin (n + 1)) :
    V⁻¹ l 0 = if l = 0 then 1 else 0 := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  have h := congrFun (congrFun (nonsing_inv_mul V hu) l) 0
  rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (n + 1)), hV.2, mul_one, Matrix.one_apply] at h
  · exact h
  · intro k _ hk; rw [hV.1 k 0 (Fin.pos_iff_ne_zero.2 hk), mul_zero]
  · simp

theorem mul_first_column_of_unit_column {n k : ℕ} (N : Matrix (Fin k) (Fin (n + 1)) R) {P : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hP : ∀ l, P l 0 = if l = 0 then 1 else 0) (i : Fin k) : (N * P) i 0 = N i 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [hP]
  · intro l _ hl; simp [hP, hl]
  · simp

theorem lastRow_mul {n k : ℕ} {Q : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hQ : IsUT Q) (N : Matrix (Fin (n + 1)) (Fin k) R)
    (j : Fin k) : (Q * N) (Fin.last n) j = N (Fin.last n) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n), hQ.2, one_mul]
  · intro l _ hl; rw [hQ.1 _ _ (Fin.lt_last_iff_ne_last.2 hl), zero_mul]
  · simp

theorem Xof_mul_entry (hU : IsUT U) (hD : IsUnit (Dof M).det) :
    Xof (U * M) (Fin.last m) 0 = Xof M (Fin.last m) 0 + Bof U (Fin.last m) 0 := by
  rw [Xof_mul M hU hD, Matrix.add_apply, mul_first_column_of_unit_column _ (inv_first_column_of_upper_triangular (Dof_isUT hU)), mul_first_column_of_unit_column _ (inv_first_column_of_upper_triangular (Dof_isUT hU)),
    lastRow_mul (Aof_isUT hU)]

theorem sd_blocks (U : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    sd U = sd (Aof U) + Bof U (Fin.last m) 0 + sd (Dof U) := by
  have e : ∀ f : Fin (m + r + 1 + 1) → R, ∑ i, f i = ∑ a, f ((eqv m r).symm a) := fun f =>
    (Equiv.sum_comp (eqv m r).symm f).symm
  rw [sd, e]
  simp only [Fintype.sum_sum_type]
  simp_rw [e, Fintype.sum_sum_type, eqv_symm_inl, eqv_symm_inr]
  have h2 : ∑ i : Fin (m + 1), ∑ j : Fin (r + 1),
      (if m + 1 + j.val = i.val + 1 then U ((eqv m r).symm (Sum.inl i)) ((eqv m r).symm (Sum.inr j)) else 0) =
      Bof U (Fin.last m) 0 := by
    rw [Finset.sum_eq_single (Fin.last m), Finset.sum_eq_single (0 : Fin (r + 1))]
    · rw [if_pos (by simp)]; rfl
    · intro j _ hj; rw [if_neg]; intro h; apply hj; ext; simp at h ⊢; omega
    · simp
    · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; rw [if_neg]; intro h; apply hi; ext; simp; omega
    · simp
  have h3 : ∑ i : Fin (r + 1), ∑ j : Fin (m + 1),
      (if j.val = m + 1 + i.val + 1 then U ((eqv m r).symm (Sum.inr i)) ((eqv m r).symm (Sum.inl j)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; omega
  have h4 : ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
      (if m + 1 + j.val = m + 1 + i.val + 1 then U ((eqv m r).symm (Sum.inr i)) ((eqv m r).symm (Sum.inr j)) else 0) =
      sd (Dof U) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j.val = i.val + 1
    · rw [if_pos (by omega), if_pos h]; rfl
    · rw [if_neg (by omega), if_neg h]
  simp only [Finset.sum_add_distrib]
  rw [h2, h3, h4, zero_add]
  rfl

end Alg

end GlobalTheory.SchurEquiv

namespace GlobalTheory.SchurEquiv

open Matrix

section Adelic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem mkGL_mem_NA {V : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) : mkGL V ∈ GlobalTheory.JSW.NA E k := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  refine ⟨fun i j h => ?_, fun i => ?_⟩ <;> rw [coe_mkGL hu]
  · exact hV.1 i j h
  · exact hV.2 i

theorem mkGL_mul {V S : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) (hS : IsUnit S.det) :
    mkGL (V * S) = mkGL V * mkGL S := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  have hVS : IsUnit (V * S).det := by rw [det_mul]; exact hu.mul hS
  apply Units.ext
  rw [Units.val_mul, coe_mkGL hVS, coe_mkGL hu, coe_mkGL hS]

theorem psi_add (a b : Ad E) : psi (a + b) = psi a * psi b := by
  simp [psi, AddChar.map_add_eq_mul]

theorem psiN_mkGL {V : Matrix (Fin k) (Fin k) (Ad E)} (hV : IsUT V) : GlobalTheory.JSW.psiN (mkGL V) = psi (sd V) := by
  have hu : IsUnit V.det := by rw [det_of_isUT hV]; exact isUnit_one
  rw [GlobalTheory.JSW.psiN, superDiag_eq_sd, coe_mkGL hu]; rfl

theorem isUnit_Scof {m r : ℕ} (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (hM : IsUnit M.det)
    (hD : IsUnit (Dof M).det) : IsUnit (Scof M).det := by
  letI := (Dof M).invertibleOfIsUnitDet hD
  have h1 : M.det = (Dof M).det * (Scof M).det := by
    have e : (blk M).det = M.det := Matrix.det_submatrix_equiv_self _ _
    rw [← e, blk_eq, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]; rfl
  rw [h1] at hM
  exact isUnit_of_mul_isUnit_right hM

end Adelic

theorem schurF_equivariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) → (∀ u ∈ GlobalTheory.JSW.NA E (r + 1), ∀ g, b₁ (u * g) = GlobalTheory.JSW.psiN u * b₁ g) → ∀ u ∈ GlobalTheory.JSW.NA E (m + r + 1 + 1), ∀ g, schurF β b₁ χ (u * g) = GlobalTheory.JSW.psiN u * schurF β b₁ χ g := by
  intro E _ _ _ m r β b₁ χ hβ hb u hu g
  have hU : IsUT (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) := hu
  have hM : IsUnit (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  set M := (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hMdef
  set U := (u : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hUdef
  unfold schurF
  rw [Units.val_mul]
  by_cases hD : IsUnit (Dof M).det
  · rw [if_pos ((isUnit_Dof_mul_iff M hU).2 hD), if_pos hD, Xof_mul_entry M hU hD, Scof_mul M hU hD, Dof_mul M hU,
      Yof_mul M hU, mkGL_mul (Aof_isUT hU) (isUnit_Scof M hM hD), mkGL_mul (Dof_isUT hU) hD,
      hβ _ (mkGL_mem_NA (Aof_isUT hU)), hb _ (mkGL_mem_NA (Dof_isUT hU)), psiN_mkGL (Aof_isUT hU),
      psiN_mkGL (Dof_isUT hU)]
    have h : GlobalTheory.JSW.psiN u = psi (sd (Aof U)) * psi (Bof U (Fin.last m) 0) * psi (sd (Dof U)) := by
      rw [GlobalTheory.JSW.psiN, superDiag_eq_sd, sd_blocks, ← psi_add, ← psi_add]; rfl
    rw [h, psi_add]; ring
  · rw [if_neg (mt (isUnit_Dof_mul_iff M hU).1 hD), if_neg hD, mul_zero]

end GlobalTheory.SchurEquiv
