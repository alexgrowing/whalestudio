import Formalism.ResultantValuation.KoszulSecondDifferential

open Matrix

noncomputable section

namespace Formalism.ResultantValuation

namespace AdjugateJacobi

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

def minorF (M : Matrix n n R) (k i l j : n) : R :=
  M.adjugate k l * M.adjugate i j - M.adjugate i l * M.adjugate k j

def minorQ (M : Matrix n n R) (k i l j : n) : R :=
  ((M.updateCol i (Pi.single j 1)).updateCol k (Pi.single l 1)).det

def twoCol (k i : n) (u v : n → R) : Matrix n n R :=
  ((1 : Matrix n n R).updateCol k u).updateCol i v

theorem det_twoCol {k i : n} (hki : k ≠ i) (u v : n → R) :
    (twoCol k i u v).det = u k * v i - u i * v k := by
  classical
  let p : n → Prop := fun a => a ≠ k ∧ a ≠ i
  have h : ∀ a, ¬p a → ∀ b, p b → twoCol k i u v a b = 0 := by
    intro a ha b hb
    have hab : a ≠ b := by
      rintro rfl
      exact ha hb
    simp only [twoCol, updateCol_ne hb.2, updateCol_ne hb.1, one_apply_ne hab]
  rw [twoBlockTriangular_det _ p h]
  have h1 : (toSquareBlockProp (twoCol k i u v) p).det = 1 := by
    have : toSquareBlockProp (twoCol k i u v) p = 1 := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      rw [toSquareBlockProp_def, of_apply]
      simp only [twoCol, updateCol_ne hb.2, updateCol_ne hb.1]
      by_cases hab : a = b
      · subst hab; simp
      · rw [one_apply_ne hab, one_apply_ne (fun h => hab (congrArg Subtype.val h))]
    rw [this, det_one]
  rw [h1, one_mul]
  let f : Fin 2 → { a // ¬p a } := ![⟨k, fun h => h.1 rfl⟩, ⟨i, fun h => h.2 rfl⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [f, Subtype.ext_iff, Ne.symm hki]
    · rintro ⟨a, ha⟩
      simp only [p, not_and_or, not_not] at ha
      rcases ha with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  let e : Fin 2 ≃ { a // ¬p a } := Equiv.ofBijective f hf
  rw [← det_submatrix_equiv_self e, det_fin_two]
  simp [e, f, toSquareBlockProp_def, twoCol, updateCol_apply, hki]
  ring

theorem mulVec_adjugate_col (M : Matrix n n R) (l : n) :
    M *ᵥ (fun r => M.adjugate r l) = M.det • Pi.single l 1 := by
  ext a
  have := congrFun (congrFun (mul_adjugate M) a) l
  rw [mul_apply, Matrix.smul_apply, one_apply, smul_eq_mul] at this
  simp only [mulVec, dotProduct, this, Pi.smul_apply, Pi.single_apply, smul_eq_mul, eq_comm]

theorem key (M : Matrix n n R) {k i : n} (hki : k ≠ i) (l j : n) :
    M.det * minorF M k i l j = M.det * (M.det * minorQ M k i l j) := by
  have hN : (twoCol k i (fun r => M.adjugate r l) (fun r => M.adjugate r j)).det =
      minorF M k i l j := by
    rw [det_twoCol hki, minorF]
  have hMN : M * twoCol k i (fun r => M.adjugate r l) (fun r => M.adjugate r j) =
      ((M.updateCol i (M.det • Pi.single j 1)).updateCol k (M.det • Pi.single l 1)) := by
    rw [twoCol, mul_updateCol, mul_updateCol, mul_one, mulVec_adjugate_col,
      mulVec_adjugate_col, updateCol_comm _ hki]
  have := congrArg det hMN
  rw [det_mul, hN, det_updateCol_smul, updateCol_comm _ (Ne.symm hki), det_updateCol_smul,
    updateCol_comm _ hki] at this
  rw [this, minorQ]

end AdjugateJacobi

end Formalism.ResultantValuation
