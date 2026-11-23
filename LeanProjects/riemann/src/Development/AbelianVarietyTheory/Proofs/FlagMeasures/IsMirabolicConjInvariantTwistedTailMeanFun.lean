import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

noncomputable section

namespace GlobalTheory.GLm.TailClass

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime] {m k : ℕ}

def dM (k : ℕ) (A : Mt g m) : Mt g (m + k) :=
  (Matrix.fromBlocks A 0 0 (1 : Mt g k)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem dM_mul (A B : Mt g m) : dM k A * dM k B = dM k (A * B) := by
  simp [dM, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem dM_one : dM k (1 : Mt g m) = 1 := by
  simp [dM, Matrix.fromBlocks_one]

def dG (k : ℕ) (p : Gn g m) : Gn g (m + k) :=
  ⟨dM k p.val, dM k p.inv, by rw [dM_mul, p.val_inv, dM_one], by rw [dM_mul, p.inv_val, dM_one]⟩

theorem conj_val (p : Gn g m) (x : Gn g (m + k)) :
    ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) =
      dM k (p : Mt g m) * (x : Mt g (m + k)) * dM k ((p⁻¹ : Gn g m) : Mt g m) := rfl

theorem tl_apply (X : Mt g (m + k)) (i j : Fin m) : tl m X i j = X (Fin.castAdd k i) (Fin.castAdd k j) := by
  have h : (i : ℕ) < m + k ∧ (j : ℕ) < m + k := ⟨by omega, by omega⟩
  rw [tl, entN, dif_pos h]; rfl

theorem upperLeftBlock_blockDiagExtendByIdentity_conj (A B : Mt g m) (X : Mt g (m + k)) : tl m (dM k A * X * dM k B) = A * tl m X * B := by
  ext i j
  simp [tl_apply, dM, Matrix.mul_apply, Fin.sum_univ_add]

theorem blockDiagExtendByIdentity_conj_upperRight_apply (A B : Mt g m) (X : Mt g (m + k)) (i : Fin m) (j : Fin k) :
    (dM k A * X * dM k B) (Fin.castAdd k i) (Fin.natAdd m j) =
      ∑ l, A i l * X (Fin.castAdd k l) (Fin.natAdd m j) := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem blockDiagExtendByIdentity_conj_lowerLeft_apply (A B : Mt g m) (X : Mt g (m + k)) (i : Fin k) (j : Fin m) :
    (dM k A * X * dM k B) (Fin.natAdd m i) (Fin.castAdd k j) =
      ∑ l, X (Fin.natAdd m i) (Fin.castAdd k l) * B l j := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem blockDiagExtendByIdentity_conj_lowerRight_apply (A B : Mt g m) (X : Mt g (m + k)) (i j : Fin k) :
    (dM k A * X * dM k B) (Fin.natAdd m i) (Fin.natAdd m j) = X (Fin.natAdd m i) (Fin.natAdd m j) := by
  simp [dM, Matrix.mul_apply, Fin.sum_univ_add, Matrix.one_apply]

theorem entN_blockDiagExtendByIdentity_conj_lowerRight (A B : Mt g m) (X : Mt g (m + k)) (i j : ℕ) (hi : m ≤ i) (hj : m ≤ j) :
    entN (dM k A * X * dM k B) i j = entN X i j := by
  unfold entN
  split_ifs with h
  · have e1 : (⟨i, h.1⟩ : Fin (m + k)) = Fin.natAdd m ⟨i - m, by omega⟩ := by ext; simp; omega
    have e2 : (⟨j, h.2⟩ : Fin (m + k)) = Fin.natAdd m ⟨j - m, by omega⟩ := by ext; simp; omega
    rw [e1, e2, blockDiagExtendByIdentity_conj_lowerRight_apply]
  · rfl

theorem inR_conj (A B : Mt g m) (X : Mt g (m + k)) (h : InR m X) : InR m (dM k A * X * dM k B) := by
  refine ⟨fun i j hj hi => ?_, ?_⟩
  · have e1 : i = Fin.natAdd m ⟨i - m, by omega⟩ := by ext; simp; omega
    have e2 : j = Fin.castAdd k ⟨j, hj⟩ := by ext; simp
    rw [e1, e2, blockDiagExtendByIdentity_conj_lowerLeft_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [h.1 _ _ (by simp) (by simp), zero_mul]
  · have : br m (m + k - m) (dM k A * X * dM k B) = br m (m + k - m) X := by
      ext i j
      exact entN_blockDiagExtendByIdentity_conj_lowerRight A B X _ _ (by omega) (by omega)
    rw [this]; exact h.2

theorem supFrom_conj (hm : 1 ≤ m) (A B : Mt g m) (hA : InMir A) (X : Mt g (m + k)) :
    supFrom (m - 1) (dM k A * X * dM k B) = supFrom (m - 1) X := by
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  by_cases h : m ≤ j
  · exact entN_blockDiagExtendByIdentity_conj_lowerRight A B X _ _ h (by omega)
  · have h' : j < m + k ∧ j + 1 < m + k := ⟨by omega, by omega⟩
    have e1 : (⟨j, h'.1⟩ : Fin (m + k)) = Fin.castAdd k ⟨j, by omega⟩ := by ext; simp
    have e2 : (⟨j + 1, h'.2⟩ : Fin (m + k)) = Fin.natAdd m ⟨0, by omega⟩ := by ext; simp; omega
    rw [entN, entN, dif_pos h', dif_pos h', e1, e2, blockDiagExtendByIdentity_conj_upperRight_apply]
    have : ∀ l, A ⟨j, by omega⟩ l = (1 : Mt g m) ⟨j, by omega⟩ l := fun l => hA _ _ (by simp; omega)
    simp [this, Matrix.one_apply]

theorem inMir_of (X : Mt g (m + k)) (h : InR m X) (h0 : InMir (tl m X)) : InMir X := by
  intro i j hi
  by_cases him : (i : ℕ) < m
  · have hj : (j : ℕ) < m := by omega
    have e1 : i = Fin.castAdd k ⟨i, him⟩ := by ext; simp
    have e2 : j = Fin.castAdd k ⟨j, hj⟩ := by ext; simp
    have := h0 ⟨i, him⟩ ⟨j, hj⟩ (by simp; omega)
    rw [tl_apply, ← e1, ← e2] at this
    rw [this]
    simp [Matrix.one_apply, Fin.ext_iff]
  · by_cases hj : (j : ℕ) < m
    · rw [h.1 i j hj (by omega), Matrix.one_apply_ne]
      intro e; subst e; omega
    · have h2 := h.2 ⟨i - m, by omega⟩ ⟨j - m, by omega⟩
      have h' : m + (i - m) < m + k ∧ m + (j - m) < m + k := ⟨by omega, by omega⟩
      have e1 : (⟨m + (i - m), h'.1⟩ : Fin (m + k)) = i := by ext; simp; omega
      have e2 : (⟨m + (j - m), h'.2⟩ : Fin (m + k)) = j := by ext; simp; omega
      simp only [br, entN, dif_pos h', e1, e2] at h2
      by_cases e : i = j
      · subst e
        rw [h2.2 rfl, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne e]
        refine h2.1 ?_
        have : (i : ℕ) ≠ j := fun h => e (Fin.ext h)
        rw [Fin.lt_def]
        simp only
        omega

theorem inMir_dM (A : Mt g m) (hA : InMir A) : InMir (dM k A) := by
  have e : dM k A = dM k A * 1 * dM k 1 := by rw [dM_one, mul_one, mul_one]
  have h1 : InR m (1 : Mt g (m + k)) := by
    refine ⟨fun i j hj hi => Matrix.one_apply_ne (by intro e; subst e; omega), fun a b => ?_⟩
    have h' : m + a < m + k ∧ m + b < m + k := ⟨by omega, by omega⟩
    simp only [br, entN, dif_pos h', Matrix.one_apply, Fin.ext_iff, Fin.lt_def]
    constructor
    · intro h; rw [if_neg (by omega)]
    · intro h; rw [if_pos (by omega)]
  have h2 : tl m (1 : Mt g (m + k)) = 1 := by
    ext i j
    simp [tl_apply, Matrix.one_apply, Fin.ext_iff]
  refine inMir_of _ (e ▸ inR_conj _ _ _ h1) ?_
  rw [e, upperLeftBlock_blockDiagExtendByIdentity_conj, h2, mul_one, mul_one]
  exact hA

theorem isMirClass_tail (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (m n : ℕ) (F : Gn g n → ℂ)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hF : IsMirClass F) : IsMirClass (tail ψ m F) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  intro p x₀ hp hx₀
  unfold tail
  congr 1
  symm
  refine Fintype.sum_equiv (MulAut.conj (dG k p)).toEquiv _ _ fun x => ?_
  have e : (MulAut.conj (dG k p)).toEquiv x = dG k p * x * (dG k p)⁻¹ := rfl
  rw [e]
  have hiff : (InR m (x : Mt g (m + k)) ∧ tl m (x : Mt g (m + k)) = (x₀ : Mt g m)) ↔
      (InR m ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) ∧
        tl m ((dG k p * x * (dG k p)⁻¹ : Gn g (m + k)) : Mt g (m + k)) = ((p * x₀ * p⁻¹ : Gn g m) : Mt g m)) := by
    rw [conj_val, upperLeftBlock_blockDiagExtendByIdentity_conj, Units.val_mul, Units.val_mul, Units.mul_left_inj, Units.mul_right_inj]
    refine and_congr_left fun _ => ⟨inR_conj _ _ _, fun h => ?_⟩
    have := inR_conj ((p⁻¹ : Gn g m) : Mt g m) (p : Mt g m) _ h
    rwa [← mul_assoc, ← mul_assoc, mul_assoc _ (dM k _) (dM k _), dM_mul, Units.inv_mul, dM_one,
      one_mul, mul_one] at this
  by_cases h : InR m (x : Mt g (m + k)) ∧ tl m (x : Mt g (m + k)) = (x₀ : Mt g m)
  · rw [if_pos h, if_pos (hiff.1 h), hF _ _ (inMir_dM _ hp) (inMir_of _ h.1 (h.2 ▸ hx₀)), conj_val,
      supFrom_conj hm _ _ hp]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

end GlobalTheory.GLm.TailClass
