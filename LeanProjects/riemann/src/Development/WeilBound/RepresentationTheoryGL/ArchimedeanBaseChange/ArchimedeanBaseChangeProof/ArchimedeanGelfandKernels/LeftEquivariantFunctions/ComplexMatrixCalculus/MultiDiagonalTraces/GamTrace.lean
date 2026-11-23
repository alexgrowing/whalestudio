import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.MultiDiagonalTraces.MtEqToMatrix

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.Cxi

private theorem gamM_mul' {n : ℕ} (A B : Matrix (Md n) (Md n) ℂ) :
    gamM (A * B) = gamM A * gamM B := by
  unfold gamM
  rw [Matrix.toLin'_mul, ← ExteriorAlgebra.map_comp_map]
  show LinearMap.toMatrix (fb n) (fb n)
      ((ExteriorAlgebra.map (toLin' A)).comp (ExteriorAlgebra.map (toLin' B))).toLinearMap =
    LinearMap.toMatrix (fb n) (fb n) (ExteriorAlgebra.map (toLin' A)).toLinearMap *
      LinearMap.toMatrix (fb n) (fb n) (ExteriorAlgebra.map (toLin' B)).toLinearMap
  rw [AlgHom.comp_toLinearMap]
  exact LinearMap.toMatrix_comp (fb n) (fb n) (fb n) _ _

private theorem gamM_one' {n : ℕ} : gamM (1 : Matrix (Md n) (Md n) ℂ) = 1 := by
  unfold gamM
  rw [Matrix.toLin'_one, ExteriorAlgebra.map_id]
  exact LinearMap.toMatrix_id _

private theorem trace_gamM_conj_eq_of_mul_eq_one {n : ℕ} (A P Q : Matrix (Md n) (Md n) ℂ) (h : Q * P = 1) :
    (gamM (P * A * Q)).trace = (gamM A).trace := by
  rw [gamM_mul', gamM_mul', Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← gamM_mul', h,
    gamM_one', Matrix.one_mul]

theorem gamTrace : GamTrace := by
  intro n z hz
  have hz0 : ∀ a, z a ≠ 0 := fun a h => by simpa [h] using hz a
  have hinv : (diagonal z)⁻¹ = diagonal (fun a => (z a)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact inv_mul_cancel₀ (hz0 a)
  have hc : ∀ a, conj (z a) = (z a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_right
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz a]
    norm_num
  rw [hinv]
  rcases isEmpty_or_nonempty (Md n) with hn | hn
  · have h0 : n = 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact h
      · exact (hn.false ⟨0, Nat.mul_pos h h⟩).elim
    subst h0
    have hM : (Mt (diagonal fun a => (z a)⁻¹))ᵀ = diagonal (fun _ => (0 : ℂ)) := by
      ext i
      exact hn.elim i
    rw [hM, Cxi.trace_gam_diag]
    simp
  · rw [Mt_eq_toMatrix,
      ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (hbB n) (stdB n) (hbB n) (stdB n),
      toMatrix_stdB, Matrix.transpose_mul, Matrix.transpose_mul, diagonal_transpose,
      ← Matrix.mul_assoc,
      trace_gamM_conj_eq_of_mul_eq_one _ _ _ (by rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
        Matrix.transpose_one]),
      Cxi.trace_gam_diag,
      Fintype.prod_equiv finProdFinEquiv.symm _
        (fun p : Fin n × Fin n => 1 + (z p.1)⁻¹ * conj ((z p.2)⁻¹)) (fun m => rfl),
      Fintype.prod_prod_type, Finset.prod_comm]
    refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => ?_))
    rw [map_inv₀, hc, inv_inv]
    ring

end PositivityTheory.RgBcC
