import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFTA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {n r t : ℕ}

abbrev ee (hn : r + t = n) : Fin r ⊕ Fin t ≃ Fin n := finSumFinEquiv.trans (finCongr hn)

abbrev ff (hn : r + t = n) : Fin t ⊕ Fin r ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))

theorem ee_inl_val (hn : r + t = n) (k : Fin r) : (ee hn (Sum.inl k) : ℕ) = k := by simp [ee]
theorem ee_inr_val (hn : r + t = n) (k : Fin t) : (ee hn (Sum.inr k) : ℕ) = r + k := by simp [ee]
theorem ff_inl_val (hn : r + t = n) (k : Fin t) : (ff hn (Sum.inl k) : ℕ) = k := by simp [ff]
theorem ff_inr_val (hn : r + t = n) (k : Fin r) : (ff hn (Sum.inr k) : ℕ) = t + k := by simp [ff]

theorem ext_ee (hn : r + t = n) {R : Type} {M N : Matrix (Fin n) (Fin n) R}
    (h : ∀ s s', M (ee hn s) (ee hn s') = N (ee hn s) (ee hn s')) : M = N := by
  ext i j
  simpa using h ((ee hn).symm i) ((ee hn).symm j)

theorem bl_ee {R : Type} (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R) (b : Matrix (Fin r) (Fin t) R)
    (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) (s s' : Fin r ⊕ Fin t) :
    bl hn a b c d (ee hn s) (ee hn s') = Matrix.fromBlocks a b c d s s' := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem blockRowSubstitution_one {R : Type} [CommRing R] (hn : r + t = n) : bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 1 = 1 := by
  refine ext_ee hn fun s s' => ?_
  rw [bl_ee, Matrix.fromBlocks_one, Matrix.one_apply, Matrix.one_apply]
  simp only [(ee hn).injective.eq_iff]

theorem bl_add {R : Type} [CommRing R] (hn : r + t = n) (a a' : Matrix (Fin r) (Fin r) R) (b b' : Matrix (Fin r) (Fin t) R)
    (c c' : Matrix (Fin t) (Fin r) R) (d d' : Matrix (Fin t) (Fin t) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  refine ext_ee hn fun s s' => ?_
  rw [Matrix.add_apply, bl_ee, bl_ee, bl_ee, ← Matrix.add_apply, Matrix.fromBlocks_add]

theorem block_neg {R : Type} [CommRing R] (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R) (b : Matrix (Fin r) (Fin t) R)
    (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) :
    -bl hn a b c d = bl hn (-a) (-b) (-c) (-d) := by
  refine ext_ee hn fun s s' => ?_
  rw [Matrix.neg_apply, bl_ee, bl_ee, ← Matrix.neg_apply, Matrix.fromBlocks_neg]

theorem block_map {R S : Type} (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R) (b : Matrix (Fin r) (Fin t) R)
    (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) (f : R → S) :
    (bl hn a b c d).map f = bl hn (a.map f) (b.map f) (c.map f) (d.map f) := by
  simp only [bl, ← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem one_sub_bl {R : Type} [CommRing R] (hn : r + t = n) :
    1 - bl hn (0 : Matrix (Fin r) (Fin r) R) 0 0 1 = bl hn 1 0 0 0 := by
  rw [← blockRowSubstitution_one hn, sub_eq_iff_eq_add, bl_add]; simp

theorem eId_eq {K : Type} [Field K] (hn : r + t = n) : eId K n r = bl hn 1 0 0 0 := by
  refine ext_ee hn fun s s' => ?_
  rw [bl_ee, eId, Matrix.diagonal_apply]
  simp only [(ee hn).injective.eq_iff]
  rcases s with k | k <;> rcases s' with k' | k' <;>
    simp [Matrix.one_apply, ee_inl_val, ee_inr_val]

theorem cT_blk4 {K : Type} [Field K] (σ : K →+* K) (A B C E : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 A B C E) = blk4 (cT σ A) (cT σ C) (cT σ B) (cT σ E) := by
  simp only [cT, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.transpose_submatrix,
    Matrix.fromBlocks_transpose]

def wE {K : Type} [Field K] (e : Matrix (Fin n) (Fin n) K) : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 (1 - e) e (-e) (1 - e)

theorem cT_one {K : Type} [Field K] (σ : K →+* K) : cT σ (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  simp [cT]

theorem cT_sub {K : Type} [Field K] (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) : cT σ (A - B) = cT σ A - cT σ B := by
  have h : (A - B).map σ = A.map σ - B.map σ := by ext; simp
  rw [cT, cT, cT, h, Matrix.transpose_sub]

theorem cT_neg {K : Type} [Field K] (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K) : cT σ (-A) = -cT σ A := by
  have h : (-A).map σ = -A.map σ := by ext; simp
  rw [cT, cT, h, Matrix.transpose_neg]

theorem block_matrix_map {R S : Type} (A B C E : Matrix (Fin n) (Fin n) R) (f : R → S) :
    (blk4 A B C E).map f = blk4 (A.map f) (B.map f) (C.map f) (E.map f) := by
  simp only [blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem wE_unit {K : Type} [Field K] (σ : K →+* K) (e : Matrix (Fin n) (Fin n) K) (he : e * e = e) (hσ : cT σ e = e) :
    IsUnit (wE e).det ∧ IsUnitary σ (PositivityTheory.GramSchwartzFunctions.EC.Jm K n) (wE e) := by
  have h1 : e * (1 - e) = 0 := by rw [Matrix.mul_sub, he, Matrix.mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [Matrix.sub_mul, he, Matrix.one_mul, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_zero]
  constructor
  · refine Matrix.isUnit_det_of_right_inverse (B := blk4 (1 - e) (-e) e (1 - e)) ?_
    rw [wE, submatrix_fromBlocks_mul, ← block_matrix_one]
    congr 1 <;> (simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, h1, h2, h3, he, neg_zero, add_zero, zero_add,
      sub_add_cancel, neg_add_cancel]; try abel)
  · unfold IsUnitary
    rw [wE, cT_blk4, cT_sub, cT_one, hσ, cT_neg, hσ, PositivityTheory.GramSchwartzFunctions.EC.Jm, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    congr 1 <;> (simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, h1, h2, h3, he, neg_zero, add_zero, zero_add,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, sub_add_cancel, neg_add_cancel]; try abel)

def πe (hn : r + t = n) : Equiv.Perm (Fin n) := (ff hn).symm.trans ((Equiv.sumComm _ _).trans (ee hn))

theorem πe_ff_inl (hn : r + t = n) (k : Fin t) : πe hn (ff hn (Sum.inl k)) = ee hn (Sum.inr k) := by
  rw [πe, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]; rfl

theorem πe_symm_ee_inl (hn : r + t = n) (k : Fin r) : (πe hn).symm (ee hn (Sum.inl k)) = ff hn (Sum.inr k) := by
  rw [Equiv.symm_apply_eq, πe, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]; rfl

theorem πe_symm_ee_inr (hn : r + t = n) (k : Fin t) : (πe hn).symm (ee hn (Sum.inr k)) = ff hn (Sum.inl k) := by
  rw [Equiv.symm_apply_eq, πe_ff_inl]

def Pm (K : Type) [Field K] (hn : r + t = n) : Matrix (Fin n) (Fin n) K := (1 : Matrix (Fin n) (Fin n) K).submatrix (πe hn) id

theorem permutation_matrix_transpose {K : Type} [Field K] (hn : r + t = n) : (Pm K hn)ᵀ = (1 : Matrix (Fin n) (Fin n) K).submatrix id (πe hn) := by
  simp [Pm, Matrix.transpose_submatrix]

theorem Pm_mul_alt {K : Type} [Field K] (hn : r + t = n) : Pm K hn * (Pm K hn)ᵀ = 1 := by
  rw [permutation_matrix_transpose, Pm]
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (πe hn) (Equiv.refl _) (πe hn)
  simpa using this

theorem T_mul_Pm {K : Type} [Field K] (hn : r + t = n) : (Pm K hn)ᵀ * Pm K hn = 1 := by
  rw [permutation_matrix_transpose, Pm]
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) id (πe hn) id
  simpa using this

theorem conj_Pm {K : Type} [Field K] (hn : r + t = n) (M : Matrix (Fin n) (Fin n) K) :
    (Pm K hn)ᵀ * M * Pm K hn = M.submatrix (πe hn).symm (πe hn).symm := by
  have e1 : M = (M.submatrix (πe hn).symm id).submatrix (πe hn) id := by ext; simp
  have e2 : M.submatrix (πe hn).symm id = (M.submatrix (πe hn).symm (πe hn).symm).submatrix id (πe hn) := by ext; simp
  rw [permutation_matrix_transpose, Pm]
  nth_rewrite 1 [e1]
  rw [Matrix.submatrix_mul_equiv (1 : Matrix (Fin n) (Fin n) K) _ id (πe hn) id, Matrix.one_mul, Matrix.submatrix_id_id, e2,
    Matrix.submatrix_mul_equiv _ (1 : Matrix (Fin n) (Fin n) K) id (πe hn) id, Matrix.mul_one, Matrix.submatrix_id_id]

theorem eId_conj {K : Type} [Field K] (hn : r + t = n) :
    (Pm K hn)ᵀ * eId K n t * Pm K hn = bl hn 0 0 0 1 := by
  rw [conj_Pm]
  refine ext_ee hn fun s s' => ?_
  rcases s with k | k <;> rcases s' with k' | k' <;>
    simp only [bl_ee, Matrix.submatrix_apply, πe_symm_ee_inl, πe_symm_ee_inr] <;>
    rw [eId, Matrix.diagonal_apply] <;>
    simp [(ff hn).injective.eq_iff, ff_inl_val, ff_inr_val, Matrix.one_apply] <;> simp [Fin.ext_iff] <;> omega

end PositivityTheory.Rg.Rsw.L.LPartFT
