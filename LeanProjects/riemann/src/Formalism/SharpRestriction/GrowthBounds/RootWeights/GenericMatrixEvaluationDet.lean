import Formalism.SharpRestriction.GrowthBounds.RootWeights.EBeta
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationBoundDetPowerFactor

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section frame

variable {R : Type*} [CommRing R] {n : ℕ} {K : Type*} [CommRing K] (j : R →+* K)
  (g0 g0inv : Matrix (Fin n) (Fin n) K)

def genericMatrixEvaluation : MvPolynomial (Fin n × Fin n) R →+* K := eval₂Hom j (fun ab => g0 ab.1 ab.2)

theorem generic_matrix_evaluation_eq : (genericMatrixEvaluation j g0).mapMatrix (genMat R n) = g0 := by
  ext a b
  simp [genericMatrixEvaluation, genMat]

theorem generic_matrix_evaluation_det : genericMatrixEvaluation j g0 (genMat R n).det = g0.det := by
  rw [RingHom.map_det, generic_matrix_evaluation_eq]

def mul_sp (h : g0 * g0inv = 1) : GLCoord R n →+* K :=
  IsLocalization.Away.lift (genMat R n).det (g := genericMatrixEvaluation j g0)
    (by rw [generic_matrix_evaluation_det]; exact Matrix.isUnit_det_of_right_inverse h)

variable {g0 g0inv}

theorem mul_sp_alg (h : g0 * g0inv = 1) (a : MvPolynomial (Fin n × Fin n) R) :
    mul_sp j g0 g0inv h (algebraMap _ (GLCoord R n) a) = genericMatrixEvaluation j g0 a :=
  IsLocalization.Away.lift_eq _ _ a

theorem mul_sp_inv (h : g0 * g0inv = 1) :
    g0.det * mul_sp j g0 g0inv h (IsLocalization.Away.invSelf (S := GLCoord R n) (genMat R n).det) = 1 := by
  have h' := congrArg (mul_sp j g0 g0inv h)
    (IsLocalization.Away.mul_invSelf (S := GLCoord R n) (genMat R n).det)
  rw [map_mul, mul_sp_alg, generic_matrix_evaluation_det, map_one] at h'
  exact h'

def mul_mL (h : g0 * g0inv = 1) : GLLaurent R n →+* LaurentPolynomial K :=
  AddMonoidAlgebra.mapRingHom ℤ (mul_sp j g0 g0inv h)

theorem mul_mL_C (h : g0 * g0inv = 1) (a : GLCoord R n) :
    mul_mL j h (LaurentPolynomial.C a) = LaurentPolynomial.C (mul_sp j g0 g0inv h a) := by
  rw [← LaurentPolynomial.single_eq_C, mul_mL, AddMonoidAlgebra.mapRingHom_single]; rfl

theorem mul_mL_T (h : g0 * g0inv = 1) (k : ℤ) :
    mul_mL j h (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  rw [LaurentPolynomial.T, mul_mL, AddMonoidAlgebra.mapRingHom_single, map_one]; rfl

theorem mul_mL_coefL (h : g0 * g0inv = 1) (a : R) :
    mul_mL j h (coefL R n a) = LaurentPolynomial.C (j a) := by
  simp [coefL, mul_mL_C, mul_sp_alg, genericMatrixEvaluation]

theorem mul_mL_gL (h : g0 * g0inv = 1) :
    (mul_mL j h).mapMatrix (gL R n) = g0.map LaurentPolynomial.C := by
  ext a b
  have := congrFun (congrFun (generic_matrix_evaluation_eq j g0) a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at this
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, gL, mul_mL_C, mul_sp_alg, this]

theorem mul_mL_gLinv (h : g0 * g0inv = 1) :
    (mul_mL j h).mapMatrix (gLinv R n) = g0inv.map LaurentPolynomial.C := by
  ext a b
  have h1 : (genericMatrixEvaluation j g0).mapMatrix (genMat R n).adjugate = g0.adjugate := by
    rw [RingHom.map_adjugate, generic_matrix_evaluation_eq]
  have h2 : g0.adjugate = g0.det • g0inv := by
    calc g0.adjugate = g0.adjugate * (g0 * g0inv) := by rw [h, mul_one]
      _ = g0.det • g0inv := by rw [← mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, one_mul]
  have := congrFun (congrFun h1 a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at this
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, gLinv, mul_mL_C, map_mul, mul_sp_alg, this, h2,
    Matrix.smul_apply, smul_eq_mul]
  rw [← map_mul, ← map_mul, ← mul_assoc, mul_comm _ g0.det, mul_sp_inv, one_mul]

theorem mul_mL_twist (h : g0 * g0inv = 1) (i : Fin n) (k : ℤ) :
    (mul_mL j h).mapMatrix (twistMat R n i k) =
      g0.map LaurentPolynomial.C * Matrix.diagonal (fun a => if a = i then LaurentPolynomial.T k else 1) *
        g0inv.map LaurentPolynomial.C := by
  rw [twistMat, map_mul, map_mul, mul_mL_gL, mul_mL_gLinv]
  congr 2
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases h2 : a = i <;> simp [h2, mul_mL_T]
  · simp [hab]

end frame

section main

variable {R : Type} [CommRing R] {ι : Type} {r : ℕ} [NeZero r] (LL : Letters ι) (S : Set ι)
  {k1 : Type} [CommRing k1]

open Classical in

def mul_ew (v : ι × Fin r) : ℤ := if v.2 = lastIdx r ∧ v.1 ∈ S then (if LL.vec v.1 then 1 else -1) else 0

def mul_dl : MvPolynomial (ι × Fin r) k1 →+* LaurentPolynomial (MvPolynomial (ι × Fin r) k1) :=
  eval₂Hom (LaurentPolynomial.C.comp C)
    (fun v => LaurentPolynomial.C (X v) * LaurentPolynomial.T (mul_ew LL S v))

theorem prod_T_eq_T_sum {B : Type*} [CommRing B] {α : Type*} (s : Finset α) (f : α → ℤ) :
    ∏ v ∈ s, (LaurentPolynomial.T (f v) : LaurentPolynomial B) = LaurentPolynomial.T (∑ v ∈ s, f v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, LaurentPolynomial.T_add]

theorem mul_eWt_eq (m : ι × Fin r →₀ ℕ) : eWt LL S m = ∑ v ∈ m.support, (m v : ℤ) * mul_ew LL S v := by
  rw [eWt, Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mul_ew]
  split_ifs <;> simp

theorem mul_dl_monomial (m : ι × Fin r →₀ ℕ) (c : k1) :
    mul_dl LL S (monomial m c) = LaurentPolynomial.C (monomial m c) * LaurentPolynomial.T (eWt LL S m) := by
  have h1 : (m.prod fun i e => (LaurentPolynomial.C (X i : MvPolynomial (ι × Fin r) k1)) ^ e) =
      LaurentPolynomial.C (monomial m (1 : k1)) := by
    rw [MvPolynomial.monomial_eq, map_mul, map_finsuppProd]
    simp
  rw [mul_dl, eval₂Hom_monomial]
  simp only [mul_pow, Finsupp.prod_mul, h1, LaurentPolynomial.T_pow]
  rw [Finsupp.prod, prod_T_eq_T_sum, ← mul_eWt_eq, ← mul_assoc, RingHom.comp_apply, ← map_mul, C_mul_monomial, mul_one]

theorem mul_dl_coeff (H : MvPolynomial (ι × Fin r) k1) (m : ι × Fin r →₀ ℕ) (k : ℤ) :
    coeff m ((mul_dl LL S H).coeff k) = if eWt LL S m = k then coeff m H else 0 := by
  classical
  induction H using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [mul_dl_monomial, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, coeff_monomial]
    by_cases hdm : d = m
    · subst hdm
      by_cases hk : eWt LL S d = k <;> simp [hk]
    · by_cases hk : eWt LL S d = k <;> simp [hk, hdm]
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_add, hp, hq]
    split_ifs <;> simp

def mul_Dg (B : Type*) [CommRing B] (r : ℕ) [NeZero r] (k : ℤ) : Matrix (Fin r) (Fin r) (LaurentPolynomial B) :=
  Matrix.diagonal (fun a => if a = lastIdx r then LaurentPolynomial.T k else 1)

open Classical in

def mul_xx (g0 g0inv : Matrix (Fin r) (Fin r) k1) (v : ι × Fin r) : MvPolynomial (ι × Fin r) k1 :=
  if v.1 ∈ S then
    (if LL.vec v.1 then ∑ a : Fin r, C (g0inv a v.2) * X (v.1, a)
     else ∑ a : Fin r, C (g0 v.2 a) * X (v.1, a))
  else X v

theorem mul_square (j : R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1) (h : g0 * g0inv = 1)
    (hK : (C : k1 →+* MvPolynomial (ι × Fin r) k1).mapMatrix g0 *
      (C : k1 →+* MvPolynomial (ι × Fin r) k1).mapMatrix g0inv = 1) :
    (eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ (mul_sp ((C : k1 →+* MvPolynomial (ι × Fin r) k1).comp j) _ _ hK))
      (fun v => LaurentPolynomial.C (mul_xx LL S g0 g0inv v))).comp (twistSub LL S (lastIdx r)) =
      (mul_dl LL S).comp (eBeta LL S j g0 g0inv) := by
  classical
  have hinv : g0inv * g0 = 1 := mul_eq_one_comm.1 h
  set mL := mul_mL ((C : k1 →+* MvPolynomial (ι × Fin r) k1).comp j) hK with hmL
  set G0L : Matrix (Fin r) (Fin r) (LaurentPolynomial (MvPolynomial (ι × Fin r) k1)) :=
    g0.map (fun x => LaurentPolynomial.C (C x)) with hG0L
  set G0iL : Matrix (Fin r) (Fin r) (LaurentPolynomial (MvPolynomial (ι × Fin r) k1)) :=
    g0inv.map (fun x => LaurentPolynomial.C (C x)) with hG0iL
  have hii : G0iL * G0L = 1 := by
    have := congrArg ((LaurentPolynomial.C.comp (C : k1 →+* MvPolynomial (ι × Fin r) k1)).mapMatrix) hinv
    rw [map_mul, map_one] at this
    exact this
  obtain ⟨TW, hTW⟩ : ∃ TW : ℤ → Matrix (Fin r) (Fin r) (LaurentPolynomial (MvPolynomial (ι × Fin r) k1)),
      ∀ k, TW k = G0L * mul_Dg _ r k * G0iL := ⟨_, fun _ => rfl⟩
  have htw : ∀ k : ℤ, mL.mapMatrix (twistMat R r (lastIdx r) k) = TW k := by
    intro k
    rw [hmL, mul_mL_twist, hTW]
    rfl
  apply MvPolynomial.ringHom_ext
  · intro a
    have := mul_mL_coefL ((C : k1 →+* MvPolynomial (ι × Fin r) k1).comp j) hK a
    simp only [RingHom.comp_apply, twistSub, eBeta, mul_dl, coe_eval₂Hom, eval₂_C]
    exact this
  · rintro ⟨l, c⟩
    simp only [RingHom.comp_apply]
    by_cases hS : l ∈ S
    · by_cases hv : LL.vec l = true
      · have e1 : twistSub LL S (lastIdx r) (X (l, c) : MvPolynomial (ι × Fin r) R) =
            ∑ b : Fin r, C (twistMat R r (lastIdx r) 1 b c) * X (l, b) := by
          simp [twistSub, hS, hv]
        have e2 : eBeta LL S j g0 g0inv (X (l, c) : MvPolynomial (ι × Fin r) R) =
            ∑ a : Fin r, C (g0inv a c) * X (l, a) := by
          simp [eBeta, hS, hv]
        have hx : ∀ b, LaurentPolynomial.C (mul_xx LL S g0 g0inv (l, b)) =
            ∑ a, LaurentPolynomial.C (X (l, a)) * G0iL a b := by
          intro b
          simp [mul_xx, hS, hv, hG0iL, mul_comm]
        have ht : ∀ b, mL (twistMat R r (lastIdx r) 1 b c) = TW 1 b c :=
          fun b => congrFun (congrFun (htw 1) b) c
        have hm : Matrix.vecMul (Matrix.vecMul (fun a => LaurentPolynomial.C (X (l, a))) G0iL) (TW 1) =
            Matrix.vecMul (fun a => LaurentPolynomial.C (X (l, a)))
              (mul_Dg _ r 1 * G0iL) := by
          rw [hTW, Matrix.vecMul_vecMul, mul_assoc G0L, ← mul_assoc G0iL, hii, one_mul]
        have hm' := congrFun hm c
        simp only [Matrix.vecMul, dotProduct, mul_Dg, Matrix.diagonal_mul] at hm'
        rw [e1, e2]
        simp only [map_sum, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X, mul_dl, hx]
        have ht' : ∀ b, (AddMonoidAlgebra.mapRingHom ℤ
            (mul_sp ((C : k1 →+* MvPolynomial (ι × Fin r) k1).comp j) _ _ hK))
            (twistMat R r (lastIdx r) 1 b c) = _ := ht
        simp only [ht']
        simp only [mul_comm (TW 1 _ c)]
        rw [hm']
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : a = lastIdx r
        · simp [ha, mul_ew, hS, hv, hG0iL]; ring
        · simp [ha, mul_ew, hG0iL]; ring
      · have hv' : LL.vec l = false := by simpa using hv
        have e1 : twistSub LL S (lastIdx r) (X (l, c) : MvPolynomial (ι × Fin r) R) =
            ∑ b : Fin r, C (twistMat R r (lastIdx r) (-1) c b) * X (l, b) := by
          simp [twistSub, hS, hv']
        have e2 : eBeta LL S j g0 g0inv (X (l, c) : MvPolynomial (ι × Fin r) R) =
            ∑ a : Fin r, C (g0 c a) * X (l, a) := by
          simp [eBeta, hS, hv']
        have hx : ∀ b, LaurentPolynomial.C (mul_xx LL S g0 g0inv (l, b)) =
            ∑ a, G0L b a * LaurentPolynomial.C (X (l, a)) := by
          intro b
          simp [mul_xx, hS, hv', hG0L]
        have ht : ∀ b, mL (twistMat R r (lastIdx r) (-1) c b) = TW (-1) c b :=
          fun b => congrFun (congrFun (htw (-1)) c) b
        have hm : Matrix.mulVec (TW (-1))
            (Matrix.mulVec G0L (fun a => LaurentPolynomial.C (X (l, a)))) =
            Matrix.mulVec (G0L * mul_Dg _ r (-1))
              (fun a => LaurentPolynomial.C (X (l, a))) := by
          rw [hTW, Matrix.mulVec_mulVec, mul_assoc _ G0iL, hii, mul_one]
        have hm' := congrFun hm c
        simp only [Matrix.mulVec, dotProduct, mul_Dg, Matrix.mul_diagonal] at hm'
        rw [e1, e2]
        simp only [map_sum, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X, mul_dl, hx]
        have ht' : ∀ b, (AddMonoidAlgebra.mapRingHom ℤ
            (mul_sp ((C : k1 →+* MvPolynomial (ι × Fin r) k1).comp j) _ _ hK))
            (twistMat R r (lastIdx r) (-1) c b) = _ := ht
        simp only [ht']
        rw [hm']
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : a = lastIdx r
        · simp [ha, mul_ew, hS, hv', hG0L]; ring
        · simp [ha, mul_ew, hG0L]
    · have e1 : twistSub LL S (lastIdx r) (X (l, c) : MvPolynomial (ι × Fin r) R) = X (l, c) := by
        simp [twistSub, hS]
      have e2 : eBeta LL S j g0 g0inv (X (l, c) : MvPolynomial (ι × Fin r) R) = X (l, c) := by
        simp [eBeta, hS]
      rw [e1, e2]
      simp [mul_dl, mul_xx, mul_ew, hS]

end main

theorem hSupp_proved : HSupp := by
  intro R _ ι _ LL r _ S k1 _ j g0 g0inv h G th hth m hm
  have hK : (C : k1 →+* MvPolynomial (ι × Fin r) k1).mapMatrix g0 *
      (C : k1 →+* MvPolynomial (ι × Fin r) k1).mapMatrix g0inv = 1 := by rw [← map_mul, h, map_one]
  have hsq := RingHom.congr_fun (mul_square LL S j g0 g0inv h hK) G
  simp only [RingHom.comp_apply] at hsq
  have hsub := mul_Psi_support (mul_sp ((C : k1 →+* MvPolynomial (ι × Fin r) k1).comp j) _ _ hK)
    (mul_xx LL S g0 g0inv) (twistSub LL S (lastIdx r) G)
  have hmem : eWt LL S m ∈ sDegs LL S (lastIdx r) G := by
    apply hsub
    rw [Finsupp.mem_support_iff, hsq]
    intro h0
    have h1 := mul_dl_coeff LL S (eBeta LL S j g0 g0inv G) m (eWt LL S m)
    rw [h0, if_pos rfl] at h1
    exact (MvPolynomial.mem_support_iff.1 hm) (by simpa using h1.symm)
  have h2 := hth.trans (Finset.inf_le (f := fun k : ℤ => (k : WithTop ℤ)) hmem)
  exact_mod_cast h2

end Formalism.MainNotions.G.GLWeightTheory
