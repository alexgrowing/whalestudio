import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.TransferFactor

variable {k : Type} [CommRing k] {r : ℕ}

theorem full_cc (Y : Gl r k) (a b : Fin r) : full Y (Fin.castSucc a) (Fin.castSucc b) = Y.1 a b := by
  simp [full, finSumFinEquiv_symm_apply_castSucc]

theorem full_lc (Y : Gl r k) (b : Fin r) : full Y (Fin.last r) (Fin.castSucc b) = Y.2.2.1 b := by
  simp [full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

def vrow (Y : Gl r k) (i : ℕ) : Fin (r + 1) → k := Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ i)

theorem vrow_succ_cast (Y : Gl r k) (i : ℕ) (j : Fin r) :
    vrow Y (i + 1) (Fin.castSucc j) =
      ((fun l => vrow Y i (Fin.castSucc l)) ᵥ* Y.1) j + vrow Y i (Fin.last r) * Y.2.2.1 j := by
  simp only [vrow, pow_succ, ← Matrix.vecMul_vecMul]
  rw [Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc]
  simp only [full_cc, full_lc]
  rfl

theorem vrow_poly (Y : Gl r k) (i : ℕ) : ∃ p : Polynomial k, p.coeff i = 1 ∧ (∀ N, i < N → p.coeff N = 0) ∧
    (fun l => vrow Y (i + 1) (Fin.castSucc l)) = Y.2.2.1 ᵥ* Polynomial.aeval Y.1 p := by
  induction i with
  | zero =>
    refine ⟨1, by simp, fun N hN => ?_, ?_⟩
    · rw [Polynomial.coeff_one]; simp; omega
    · funext l
      rw [vrow_succ_cast]
      simp [vrow, Pi.single_apply, Fin.castSucc_ne_last, Matrix.vecMul, dotProduct, Matrix.one_apply_ne' (Fin.castSucc_ne_last _), Matrix.one_apply]
  | succ i ih =>
    obtain ⟨p, h1, h2, h3⟩ := ih
    refine ⟨p * Polynomial.X + Polynomial.C (vrow Y (i + 1) (Fin.last r)), ?_, fun N hN => ?_, ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_C, h1]; simp
    · rw [Polynomial.coeff_add, Polynomial.coeff_C]
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Polynomial.coeff_mul_X, h2 M (by omega)]; simp
    · funext l
      rw [vrow_succ_cast, h3]
      simp [map_add, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.vecMul_add, Matrix.vecMul_vecMul,
        Algebra.algebraMap_eq_smul_one, Matrix.vecMul_smul, mul_comm]

theorem lastDet_eq (Y : Gl r k) : lastDet Y = (-1) ^ r * (Cm Y).det := by
  classical
  choose p hp1 hp2 hp3 using vrow_poly Y
  let T : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => (p i).coeff j
  have hT : T.det = 1 := by
    rw [Matrix.det_of_lowerTriangular T (fun i j hij => hp2 i j hij)]
    exact Finset.prod_eq_one fun i _ => hp1 i
  have hmin : (Matrix.of fun (i j : Fin r) => vrow Y ((i : ℕ) + 1) (Fin.castSucc j)) = T * Cm Y := by
    ext i j
    have hd : (p i).natDegree < r := lt_of_le_of_lt
      (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (hp2 i)) i.2
    rw [Matrix.of_apply, congrFun (hp3 i) j, Polynomial.aeval_eq_sum_range' hd, Finset.sum_range
      (fun l => (p i).coeff l • Y.1 ^ l), Matrix.vecMul_sum]
    simp [Matrix.mul_apply, T, Cm, Matrix.vecMul_smul, Finset.sum_apply, mul_comm]
  unfold lastDet
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_castSucc]
  have hz : ∀ j : Fin r, (Matrix.of fun (i j : Fin (r + 1)) =>
      (Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ (i : ℕ))) j) 0 (Fin.castSucc j) = 0 := by
    intro j; simp [Pi.single_apply, Fin.castSucc_ne_last, Matrix.one_apply_ne' (Fin.castSucc_ne_last _)]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  rw [show (Matrix.of fun (i j : Fin (r + 1)) =>
      (Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ (i : ℕ))) j) 0 (Fin.last r) = 1 by simp]
  rw [Fin.succAbove_last]
  have hs : ((Matrix.of fun (i j : Fin (r + 1)) =>
      (Pi.single (Fin.last r) (1 : k) ᵥ* (full Y ^ (i : ℕ))) j).submatrix Fin.succ Fin.castSucc) =
      Matrix.of fun (i j : Fin r) => vrow Y ((i : ℕ) + 1) (Fin.castSucc j) := by
    ext i j; simp [vrow]
  rw [hs, hmin, Matrix.det_mul, hT, Fin.val_last]; ring

theorem Cm_act (g : GL (Fin r) k) (Y : Gl r k) :
    Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  ext i j
  simp only [Cm, act, Matrix.of_apply, Units.conj_pow, Matrix.mul_apply]
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_vecMul _ _ (g : Matrix (Fin r) (Fin r) k)]
  rw [show ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) * (g : Matrix (Fin r) (Fin r) k) = 1 from
    Units.inv_mul g, Matrix.vecMul_one]
  simp [Matrix.vecMul, dotProduct, Cm]

end GlobalTheory.JR.TransferFactor

theorem GlobalTheory.JR.transfer_factor_lemma : ∀ (k : Type) [CommRing k] (r : ℕ), (∀ Y : Gl r k, lastDet Y = (-1) ^ r * (Cm Y).det) ∧ ∀ (g : GL (Fin r) k) (Y : Gl r k), Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) :=
  fun _ _ _ => ⟨GlobalTheory.JR.TransferFactor.lastDet_eq, GlobalTheory.JR.TransferFactor.Cm_act⟩
