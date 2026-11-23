import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondEmbedMulFirstEmbedApply

namespace Formalism.FourierDecayAlt.P.Wd9

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section Basic

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))

theorem ins_smul (a : S) (c : K) (M : M2 (SlopeTestRemainingChoices S A)) : ins a (c • M) = c • ins a M := by
  simp only [ins, Finset.smul_sum, Matrix.smul_apply, mul_smul_comm]

theorem ins_neg (a : S) (M : M2 (SlopeTestRemainingChoices S A)) : ins a (-M) = -ins a M := by
  simp only [ins, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem free_one (a : S) : FreeOf a (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _

theorem free_zero (a : S) : FreeOf a (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _

theorem free_neg {a : S} {b : SlopeTestRemainingChoices S A} (h : FreeOf a b) : FreeOf a (-b) := fun i j => (h i j).neg_right

theorem free_smul {a : S} {b : SlopeTestRemainingChoices S A} (c : K) (h : FreeOf a b) : FreeOf a (c • b) := fun i j => (h i j).smul_right c

theorem freeOf_J_matrix (a : S) : FreeOf2 a JJ := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J] <;>
    first | exact free_zero a | exact free_one a | exact free_neg (free_one a)

theorem freeOf2_mul {a : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) (hN : FreeOf2 a N) :
    FreeOf2 a (M * N) := by
  intro i j k l
  simp only [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun m _ => (hM i m k l).mul_right (hN m j k l)

theorem freeOf2_transpose {a : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) : FreeOf2 a Mᵀ := fun i j => hM j i

theorem freeOf_matrix_neg {a : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) : FreeOf2 a (-M) := fun i j => free_neg (hM i j)

theorem freeOf_matrix_smul {a : S} {M : M2 (SlopeTestRemainingChoices S A)} (c : K) (hM : FreeOf2 a M) : FreeOf2 a (c • M) := fun i j => free_smul c (hM i j)

theorem freeOf_diagScalar {a : S} {b : SlopeTestRemainingChoices S A} (h : FreeOf a b) : FreeOf2 a (d0 b) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simpa [d0] using h
  · simpa [d0, hij] using free_zero (A := A) a

theorem J_mul_J : JJ * JJ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]

theorem J_transpose : JJᵀ = -JJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J]

theorem J_conjTranspose [StarRing A] : JJᴴ = -JJ := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J]

theorem comm_J (b : SlopeTestRemainingChoices S A) (i j : Fin 2) : Commute b (JJ i j) := by
  fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J]

theorem diagScalar_mul (x y : SlopeTestRemainingChoices S A) : d0 (x * y) = d0 x * d0 y := by
  simp [d0, Matrix.diagonal_mul_diagonal]

theorem diagScalar_smul (c : K) (x : SlopeTestRemainingChoices S A) : d0 (c • x) = c • d0 x := by
  funext i j
  by_cases h : i = j
  · subst h
    simp [d0]
  · simp [d0, Matrix.diagonal_apply_ne _ h]

theorem diagScalar_neg (x : SlopeTestRemainingChoices S A) : d0 (-x) = -d0 x := by
  simp [d0, Matrix.diagonal_neg]

theorem diagScalar_commute_of_entries {b : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (h : ∀ i j, Commute b (M i j)) :
    d0 b * M = M * d0 b := by
  funext i j
  simp [d0, Matrix.diagonal_mul, Matrix.mul_diagonal, (h i j).eq]

theorem ins_J (a : S) : ins a JJ = eU a 0 1 - eU a 1 0 := by
  simp [ins, Formalism.YangianSpanCharacter.T.J, Fin.sum_univ_two, sub_eq_add_neg]

theorem flip_mul_J_insert (a : S) : P0 a * d0 (ins a JJ) = d0 (ins a JJ) * (1 - Q0 a) := by
  ext i j
  rw [d0, Matrix.diagonal_mul, Matrix.mul_diagonal, ins_J]
  fin_cases i <;> fin_cases j <;>
    simp [P0, Q0, mul_sub, sub_mul, Wd1.eU_mul_eU]

theorem partial_flip_mul_J_insert (a : S) : Q0 a * d0 (ins a JJ) = d0 (ins a JJ) * (1 - P0 a) := by
  ext i j
  rw [d0, Matrix.diagonal_mul, Matrix.mul_diagonal, ins_J]
  fin_cases i <;> fin_cases j <;>
    simp [P0, Q0, mul_sub, sub_mul, Wd1.eU_mul_eU]

theorem Rh0_J (a : S) (D d : K) (h : d = 1 - D) (hD : D ≠ 0) (hD1 : D ≠ 1) :
    Rh0 a D * d0 (ins a JJ) = (D / (D - 1)) • (d0 (ins a JJ) * Rht0 a d) := by
  have h1 : D - 1 ≠ 0 := sub_ne_zero.mpr hD1
  have hc : D / (D - 1) * (1 - D - 1)⁻¹ = -(D - 1)⁻¹ := by
    rw [show 1 - D - 1 = -D by ring, inv_neg]
    field_simp
  subst h
  unfold Rh0 Rht0
  rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, flip_mul_J_insert, Matrix.mul_smul,
    smul_smul, hc, neg_smul, ← smul_neg]
  congr 1
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, sub_smul, one_smul]
  abel

theorem Rht0_J (a : S) (d D : K) (h : D = 1 - d) (hd : d ≠ 0) (hd1 : d ≠ 1) :
    Rht0 a d * d0 (ins a JJ) = (d / (d - 1)) • (d0 (ins a JJ) * Rh0 a D) := by
  have h1 : d - 1 ≠ 0 := sub_ne_zero.mpr hd1
  have hc : d / (d - 1) * (1 - d - 1)⁻¹ = -(d - 1)⁻¹ := by
    rw [show 1 - d - 1 = -d by ring, inv_neg]
    field_simp
  subst h
  unfold Rh0 Rht0
  rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, partial_flip_mul_J_insert, Matrix.mul_smul,
    smul_smul, hc, neg_smul, ← smul_neg]
  congr 1
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, sub_smul, one_smul]
  abel

end Basic

section Main

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))

theorem alg_smul (c : K) (M : M2 (SlopeTestRemainingChoices S A)) : algebraMap K (SlopeTestRemainingChoices S A) c • M = c • M := by
  funext i j
  simp [Algebra.smul_def]

theorem mul_ins {a : S} {RR : SlopeTestRemainingChoices S A} (hR : FreeOf a RR) (M : M2 (SlopeTestRemainingChoices S A)) :
    RR * ins a M = ins a (d0 RR * M) := by
  rw [Wd1.ins_mul a _ _ (freeOf_diagScalar hR), Wd1.insert_diagonal_extract]

theorem star_mul_ins {a : S} {RR : SlopeTestRemainingChoices S A} (hR : FreeOf a RR) {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M)
    (h : (d0 RR * M)ᴴ = d0 RR * M) : star (RR * ins a M) = RR * ins a M := by
  rw [mul_ins hR, Wd1.ins_star a _ (freeOf2_mul (freeOf_diagScalar hR) hM), h]

theorem herm_transpose {RR : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)}
    (h : (d0 RR * M)ᴴ = d0 RR * M) : (d0 RR * Mᵀ)ᴴ = d0 RR * Mᵀ := by
  refine Matrix.ext fun i j => ?_
  have h1 := congrFun (congrFun h j) i
  rw [Matrix.conjTranspose_apply, d0, Matrix.diagonal_mul] at h1
  rw [Matrix.conjTranspose_apply, d0, Matrix.diagonal_mul, Matrix.diagonal_mul,
    Matrix.transpose_apply, Matrix.transpose_apply]
  rw [Matrix.diagonal_mul] at h1
  exact h1

theorem ins_J_comm {a : S} {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) : b * ins a JJ = ins a JJ * b :=
  (Wd1.ins_comm a JJ b hb (comm_J b)).eq

theorem psiP_eq (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Y : K) :
    PsiP TT q a Y = -((q Y)⁻¹ • (ins a JJ * ins a (TT (Y + 1))ᵀ)) := by
  rw [PsiP, ins_neg, ins_smul, Wd1.ins_mul a _ _ (freeOf_J_matrix a)]

theorem psiM_eq (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Yb : K) :
    PsiM TT q a Yb = (q (Yb - 1))⁻¹ • (ins a JJ * ins a (TT (Yb - 1))) := by
  rw [PsiM, ins_smul, Wd1.ins_mul a _ _ (freeOf_J_matrix a)]

theorem position_clauses (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Y : K)
    (hF : ∀ Y, FreeOf2 a (TT Y)) (hdet : DetAt TT q Y) (hq : q Y ≠ 0) :
    ins a (TT Y) * PsiP TT q a Y = ins a JJᵀ ∧
    PsiP TT q a Y * ins a (JJ * TT Y) = 1 ∧
    ins a (JJ * TT Y) * PsiP TT q a Y = 1 := by
  obtain ⟨h1, h2⟩ := hdet
  rw [alg_smul] at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [PsiP, ← Wd1.ins_mul a _ _ (hF Y)]
    congr 1
    rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, h2, smul_smul, inv_mul_cancel₀ hq,
      one_smul, J_transpose]
  · rw [PsiP, ← Wd1.ins_mul a _ _
      (freeOf_matrix_neg (freeOf_matrix_smul _ (freeOf2_mul (freeOf_J_matrix a) (freeOf2_transpose (hF (Y + 1))))))]
    rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ JJ, h1,
      Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hq, one_smul, J_mul_J, neg_neg, Wd1.ins_one]
  · rw [PsiP, ← Wd1.ins_mul a _ _ (freeOf2_mul (freeOf_J_matrix a) (hF Y))]
    rw [Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_assoc, ← Matrix.mul_assoc (TT Y), h2,
      Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hq, one_smul, J_mul_J, neg_neg, Wd1.ins_one]

theorem dualPlus_of (hE : ExchMinus) : DualPlus := by
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q a Y hM hR hF hY hY1 hYr hq
  obtain ⟨c1, c2, c3⟩ := position_clauses TT q a Y hF (hM.det Y hY hY1) hq
  have hH : star (RR * ins a (TT Y)) = RR * ins a (TT Y) :=
    star_mul_ins hR (hF Y) (hM.herm Y hY hYr)
  have c4 : star (PsiP TT q a Y) * (RR * ins a (TT Y)) = ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) * RR := by
    rw [← hH, ← star_mul, mul_assoc, c1, star_mul, hM.form_herm,
      Wd1.ins_star a _ (freeOf2_transpose (freeOf_J_matrix a)), J_transpose, Matrix.conjTranspose_neg,
      J_conjTranspose, neg_neg]
  refine ⟨c1, c2, c3, c4, ?_, ?_⟩
  · rw [c4, ← ins_J_comm hR, mul_assoc, PsiP, ← Wd1.ins_mul a _ _ (freeOf_J_matrix a), Matrix.mul_neg,
      Matrix.mul_smul, ← Matrix.mul_assoc, J_mul_J, Matrix.neg_mul, Matrix.one_mul, smul_neg, neg_neg,
      ins_smul, mul_smul_comm]
  · intro Y0 hY0 hD1 hD0
    have hex := hE K A S Ω RR TT q a Y0 (Y + 1) hM hF hY0 hY1
    have hc : d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) * TT Y0 = TT Y0 * d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) :=
      diagScalar_commute_of_entries fun i j => (Wd1.ins_comm a _ (TT Y0 i j) (hF Y0 i j) (comm_J _)).symm
    have hk := Rh0_J (A := A) a (Y0 - Y) (Y + 1 - Y0) (by ring) hD0 hD1
    rw [psiP_eq, diagScalar_neg, diagScalar_smul, diagScalar_mul]
    generalize d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) = Jd at hc hk ⊢
    generalize d0 (ins a (TT (Y + 1))ᵀ) = Td at hex ⊢
    generalize (Rht0 a (Y + 1 - Y0) : M2 (SlopeTestRemainingChoices S A)) = R at hex hk ⊢
    generalize (Y0 - Y) / (Y0 - Y - 1) = c at hk ⊢
    calc TT Y0 * Rh0 a (Y0 - Y) * -((q Y)⁻¹ • (Jd * Td))
        = -((q Y)⁻¹ • (TT Y0 * (Rh0 a (Y0 - Y) * Jd) * Td)) := by
          simp only [Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_assoc]
      _ = -((q Y)⁻¹ • c • ((TT Y0 * Jd) * R * Td)) := by
          rw [hk]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = -((q Y)⁻¹ • c • (Jd * (TT Y0 * R * Td))) := by
          rw [← hc]; simp only [Matrix.mul_assoc]
      _ = -((q Y)⁻¹ • c • (Jd * (Td * R * TT Y0))) := by rw [hex]
      _ = c • (-((q Y)⁻¹ • (Jd * Td)) * (R * TT Y0)) := by
          simp only [Matrix.neg_mul, Matrix.smul_mul, smul_neg, Matrix.mul_assoc]
          rw [smul_comm]

theorem dualMinus_of (hE : ExchPlus) : DualMinus := by
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q a Yb hM hR hF hYb hYb1 hYr hq
  have hdet : DetAt TT q (Yb - 1) := hM.det (Yb - 1) hYb1 (by rwa [sub_add_cancel])
  obtain ⟨-, c2, c3⟩ := position_clauses TT q a (Yb - 1) hF hdet hq
  obtain ⟨h1, -⟩ := hdet
  rw [alg_smul, sub_add_cancel] at h1
  have hH : star (RR * ins a (TT Yb)ᵀ) = RR * ins a (TT Yb)ᵀ :=
    star_mul_ins hR (freeOf2_transpose (hF Yb)) (herm_transpose (hM.herm Yb hYb hYr))
  have hP : PsiM TT q a Yb = (q (Yb - 1))⁻¹ • ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * TT (Yb - 1)) := by
    rw [PsiM, ins_smul]
  have c0 : ins a (TT Yb)ᵀ * PsiM TT q a Yb = ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) := by
    rw [PsiM, ← Wd1.ins_mul a _ _ (freeOf2_transpose (hF Yb)), Matrix.mul_smul, ← Matrix.mul_assoc, h1,
      smul_smul, inv_mul_cancel₀ hq, one_smul]
  have c4 : star (PsiM TT q a Yb) * (RR * ins a (TT Yb)ᵀ) = ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ * RR := by
    rw [← hH, ← star_mul, mul_assoc, c0, star_mul, hM.form_herm,
      Wd1.ins_star a _ (freeOf_J_matrix a), J_transpose, J_conjTranspose]
  refine ⟨?_, c4, ?_, ?_⟩
  · refine ⟨⟨PsiM TT q a Yb, q (Yb - 1) • PsiP TT q a (Yb - 1), ?_, ?_⟩, rfl⟩
    · rw [hP, smul_mul_smul_comm, c3, inv_mul_cancel₀ hq, one_smul]
    · rw [hP, smul_mul_smul_comm, c2, mul_inv_cancel₀ hq, one_smul]
  · rw [c4, J_transpose, ins_neg, neg_mul, ← ins_J_comm hR, neg_mul, mul_assoc, PsiM,
      ← Wd1.ins_mul a _ _ (freeOf_J_matrix a), Matrix.mul_smul, ← Matrix.mul_assoc, J_mul_J, Matrix.neg_mul,
      Matrix.one_mul, smul_neg, ins_neg, mul_neg, neg_neg, ins_smul, mul_smul_comm]
  · intro Y0 hY0 hd1 hd0
    have hex := hE K A S Ω RR TT q a Y0 (Yb - 1) hM hF hY0 hYb1
    rw [show Y0 - (Yb - 1) = Y0 - Yb + 1 by ring] at hex
    have hc : d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) * TT Y0 = TT Y0 * d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) :=
      diagScalar_commute_of_entries fun i j => (Wd1.ins_comm a _ (TT Y0 i j) (hF Y0 i j) (comm_J _)).symm
    have hd0' : Yb - Y0 ≠ 0 := fun h => hd0 (by rw [← neg_sub, h, neg_zero])
    have hk := Rht0_J (A := A) a (Yb - Y0) (Y0 - Yb + 1) (by ring) hd0' hd1
    rw [show (Yb - Y0) / (Yb - Y0 - 1) = (Y0 - Yb) / (Y0 - Yb + 1) by
      rw [← neg_div_neg_eq]; congr 1 <;> ring] at hk
    rw [psiM_eq, diagScalar_smul, diagScalar_mul]
    generalize d0 (ins a (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))) = Jd at hc hk ⊢
    generalize d0 (ins a (TT (Yb - 1))) = Td at hex ⊢
    generalize (Rh0 a (Y0 - Yb + 1) : M2 (SlopeTestRemainingChoices S A)) = R at hex hk ⊢
    generalize (Y0 - Yb) / (Y0 - Yb + 1) = c at hk ⊢
    calc Rht0 a (Yb - Y0) * TT Y0 * ((q (Yb - 1))⁻¹ • (Jd * Td))
        = (q (Yb - 1))⁻¹ • (Rht0 a (Yb - Y0) * (TT Y0 * Jd) * Td) := by
          simp only [Matrix.mul_smul, Matrix.mul_assoc]
      _ = (q (Yb - 1))⁻¹ • ((Rht0 a (Yb - Y0) * Jd) * TT Y0 * Td) := by
          rw [← hc]; simp only [Matrix.mul_assoc]
      _ = (q (Yb - 1))⁻¹ • c • (Jd * (R * TT Y0 * Td)) := by
          rw [hk]; simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (q (Yb - 1))⁻¹ • c • (Jd * (Td * TT Y0 * R)) := by rw [hex]
      _ = c • ((q (Yb - 1))⁻¹ • (Jd * Td) * (TT Y0 * R)) := by
          simp only [Matrix.smul_mul, Matrix.mul_assoc]
          rw [smul_comm]

end Main

end Formalism.FourierDecayAlt.P.Wd9

namespace Formalism.FourierDecayAlt.P

theorem duality_plus : Formalism.FourierDecayAlt.Wd.DualPlus := Wd9.dualPlus_of exchange_relation_minus

theorem duality_minus : Formalism.FourierDecayAlt.Wd.DualMinus := Wd9.dualMinus_of exchange_relation_plus

end Formalism.FourierDecayAlt.P
