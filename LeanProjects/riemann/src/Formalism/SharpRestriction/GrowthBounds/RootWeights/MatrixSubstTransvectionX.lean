import Formalism.SharpRestriction.GrowthBounds.RootWeights.TwistSubEqMatrixSubst

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G

def sourceVar {ι : Type*} {n : ℕ} (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n :=
  if LL.vec l then (l, b) else (l, a)

def targetVar {ι : Type*} {n : ℕ} (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n :=
  if LL.vec l then (l, a) else (l, b)

def letterSign (B : Type*) [CommRing B] {ι : Type*} (LL : Letters ι) (l : ι) : B := if LL.vec l then 1 else -1

theorem sourceVar_fst {ι : Type*} {n : ℕ} (LL : Letters ι) (a b : Fin n) (l : ι) : (sourceVar LL a b l).1 = l := by
  unfold sourceVar
  split_ifs <;> rfl

section X

variable {R B : Type*} [CommRing R] [CommRing B] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
  (φ : R →+* B) (a b : Fin n) (t : B)

theorem sum_C_one_col (l : ι) (c : Fin n) :
    ∑ b' : Fin n, C ((1 : Matrix (Fin n) (Fin n) B) b' c) * (X (l, b') : MvPolynomial (ι × Fin n) B) = X (l, c) := by
  rw [Finset.sum_eq_single c]
  · simp
  · intro b' _ hb
    simp [Matrix.one_apply_ne hb]
  · simp

theorem sum_C_one_row (l : ι) (c : Fin n) :
    ∑ b' : Fin n, C ((1 : Matrix (Fin n) (Fin n) B) c b') * (X (l, b') : MvPolynomial (ι × Fin n) B) = X (l, c) := by
  rw [Finset.sum_eq_single c]
  · simp
  · intro b' _ hb
    simp [Matrix.one_apply_ne (Ne.symm hb)]
  · simp

theorem sum_C_single_col (s : B) (l : ι) (c : Fin n) :
    ∑ b' : Fin n, C (Matrix.single a b s b' c) * (X (l, b') : MvPolynomial (ι × Fin n) B) =
      if c = b then C s * X (l, a) else 0 := by
  by_cases hc : c = b
  · subst hc
    rw [Finset.sum_eq_single a]
    · simp
    · intro b' _ hb
      simp [Ne.symm hb]
    · simp
  · simp [hc, Ne.symm hc]

theorem sum_C_single_row (s : B) (l : ι) (c : Fin n) :
    ∑ b' : Fin n, C (Matrix.single a b s c b') * (X (l, b') : MvPolynomial (ι × Fin n) B) =
      if c = a then C s * X (l, b) else 0 := by
  by_cases hc : c = a
  · subst hc
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb
      simp [Ne.symm hb]
    · simp
  · simp [hc, Ne.symm hc]

open Classical in
theorem matrixSubst_transvection_X (v : ι × Fin n) :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (X v) =
      if v.1 ∈ S ∧ v = sourceVar LL a b v.1 then X v + C (letterSign B LL v.1 * t) * X (targetVar LL a b v.1) else X v := by
  obtain ⟨l, c⟩ := v
  rw [matrixSubst_X]
  simp only [Matrix.transvection, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib,
    sum_C_one_col, sum_C_one_row, sum_C_single_col, sum_C_single_row, sourceVar, targetVar, letterSign]
  by_cases hS : l ∈ S <;> by_cases hv : LL.vec l <;> simp [hS, hv]
  all_goals split_ifs <;> simp

end X

section fs

variable {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (a b : Fin n)

open Classical in
theorem sum_single_sourceVar_apply (c : ι → ℕ) (v : ι × Fin n) :
    (∑ l : ι, Finsupp.single (sourceVar LL a b l) (c l)) v = if v = sourceVar LL a b v.1 then c v.1 else 0 := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single v.1]
  · rw [Finsupp.single_apply]
    by_cases h : v = sourceVar LL a b v.1
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  · intro l _ hl
    rw [Finsupp.single_apply, if_neg]
    intro h
    apply hl
    rw [← h, sourceVar_fst]
  · intro h
    exact absurd (Finset.mem_univ _) h

end fs

end Formalism.MainNotions.G.GLWeightTheory
