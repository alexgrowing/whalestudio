import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts

open Polynomial UpperTheory.V.Af Formalism.ConjugateSelfDual
open scoped Matrix

namespace UpperTheory.V.Sd

private theorem det_scalar_sub_symmetric_square (S : Type) [CommRing S] (x e : S) (g : Matrix (Fin 2) (Fin 2) S) :
    (Matrix.scalar (Fin 3) x - e • symSquareMatrixHom S g).det =
      x ^ 3 - e * (g.trace ^ 2 - g.det) * x ^ 2 + e * (g.trace ^ 2 - g.det) * (e * g.det) * x - (e * g.det) ^ 3 := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_three]
  simp [symSquareMatrixHom, Matrix.scalar_apply]
  ring

private noncomputable def a0F {S : Type} [CommRing S] (u : S) : S[X] :=
  X ^ 3 + C (-u) * X ^ 2 + C u * X ^ 1 + C (-1) * X ^ 0

private theorem adjoint_square_charpoly (S : Type) [CommRing S] (e : S) (g : Matrix (Fin 2) (Fin 2) S) (he : e * g.det = 1) :
    (e • symSquareMatrixHom S g).charpoly = a0F (e * g.trace ^ 2 - 1) := by
  have h : Matrix.charmatrix (e • symSquareMatrixHom S g) = Matrix.scalar (Fin 3) X - C e • symSquareMatrixHom S[X] (g.map C) := by
    unfold Matrix.charmatrix
    congr 1
    ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom, map_ofNat]
  have hd : (g.map C).det = C g.det := by
    simp [Matrix.det_fin_two]
  have ht : (g.map C).trace = C g.trace := by
    simp [Matrix.trace_fin_two]
  have he' : C e * C g.det = 1 := by rw [← map_mul, he, map_one]
  rw [Matrix.charpoly, h, det_scalar_sub_symmetric_square, hd, ht, mul_sub (C e), he']
  simp only [a0F, map_sub, map_mul, map_pow, map_neg, map_one]
  ring

private theorem adjoint_charpoly_roots {S : Type} [Field S] (a b : S) (ha : a ≠ 0) (hb : b ≠ 0) :
    a0F ((a * b)⁻¹ * (a + b) ^ 2 - 1) = (X - C (a / b)) * (X - C 1) * (X - C (b / a)) := by
  have h1 : (a * b)⁻¹ * (a + b) ^ 2 - 1 = a / b + 1 + b / a := by field_simp; ring
  have h2 : C (a / b) * C (b / a) = 1 := by
    rw [← map_mul, show a / b * (b / a) = 1 by field_simp, map_one]
  rw [h1]
  simp only [a0F, map_add, map_neg, map_one]
  linear_combination (1 - X) * h2

private theorem quadratic_charpoly_coeff_difference {S : Type} [CommRing S] [Nontrivial S] (g : Matrix (Fin 2) (Fin 2) S) (a b : S) :
    g.charpoly.coeff 1 - ((X - C a) * (X - C b)).coeff 1 = -(g.trace - (a + b)) ∧
    g.charpoly.coeff 0 - ((X - C a) * (X - C b)).coeff 0 = g.det - a * b := by
  have h : (X - C a) * (X - C b) = X ^ 2 - C (a + b) * X + C (a * b) := by
    simp only [map_add, map_mul]; ring
  rw [h, Matrix.charpoly_fin_two]
  constructor
  · simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C]
    simp; ring
  · simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_zero, coeff_C]
    simp

section Rel

variable {K : Type} [NormedField K] [IsUltrametricDist K]

private def Rl (x y : K) : Prop := ‖y‖ ≤ 1 ∧ ‖x - y‖ < 1

private theorem Rl.left {x y : K} (h : Rl x y) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.2.le h.1)

private theorem Rl.mul {x y z w : K} (h : Rl x y) (h' : Rl z w) : Rl (x * z) (y * w) := by
  refine ⟨by rw [norm_mul]; exact mul_le_one₀ h.1 (norm_nonneg _) h'.1, ?_⟩
  rw [show x * z - y * w = x * (z - w) + (x - y) * w by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h.left (norm_nonneg _) h'.2
  · rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h.2 h'.1

private theorem Rl.inv {x y : K} (h : Rl x y) (hy : ‖y‖ = 1) : Rl x⁻¹ y⁻¹ := by
  have hx : ‖x‖ = 1 := by
    refine le_antisymm h.left (not_lt.mp fun hx => ?_)
    have := IsUltrametricDist.norm_add_le_max x (-(x - y))
    rw [norm_neg, show x + -(x - y) = y by ring, hy] at this
    exact absurd (max_lt hx h.2) (not_lt.mpr this)
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  refine ⟨by rw [norm_inv, hy, inv_one], ?_⟩
  rw [show x⁻¹ - y⁻¹ = -(x - y) * (x⁻¹ * y⁻¹) by field_simp; ring, norm_mul, norm_mul, norm_neg, norm_inv, norm_inv, hx, hy]
  simpa using h.2

omit [IsUltrametricDist K] in
private theorem adjoint_charpoly_coeff_close {u u' : K} (h : ‖u - u'‖ < 1) (i : ℕ) :
    ‖(a0F u).coeff i - (a0F u').coeff i‖ < 1 := by
  simp only [a0F, coeff_add, coeff_C_mul, coeff_X_pow]
  rcases i with _ | _ | _ | _ | i
  · simp
  · simpa using h
  · rw [norm_sub_rev] at h
    simpa [neg_add_eq_sub] using h
  · simp
  · simp

end Rel

private theorem adjoint_square_apply {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (s : Γ) :
    (ad0 ρ s : Matrix (Fin 3) (Fin 3) k) =
      ((ρ s : Matrix (Fin 2) (Fin 2) k).det)⁻¹ • symSquareMatrixHom k (ρ s : Matrix (Fin 2) (Fin 2) k) := by
  rw [ad0, tw_val]
  simp

private theorem adjoint_square_conjugate {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (g : GL (Fin 2) k) (s : Γ) :
    ((Units.map (symSquareMatrixHom k) g * ad0 ρ s * (Units.map (symSquareMatrixHom k) g)⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      (((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det)⁻¹ •
        symSquareMatrixHom k ((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, adjoint_square_apply, Units.val_mul, Units.val_mul, Matrix.det_units_conj, map_mul, map_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  rfl

private theorem symmetric_square_preserves_form (S : Type) [CommRing S] (g : Matrix (Fin 2) (Fin 2) S) :
    (symSquareMatrixHom S g)ᵀ * !![0, 0, -2; 0, 1, 0; -2, 0, 0] * symSquareMatrixHom S g =
      g.det ^ 2 • !![0, 0, -2; 0, 1, 0; -2, 0, 0] := by
  rw [Matrix.det_fin_two]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom] <;> ring

private theorem continuous_symmetric_square (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] : Continuous (symSquareMatrixHom S) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom] <;> fun_prop

private theorem symmetric_square_diagonal (S : Type) [CommRing S] (d : Fin 2 → S) :
    symSquareMatrixHom S (Matrix.diagonal d) = Matrix.diagonal ![d 0 ^ 2, d 0 * d 1, d 1 ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom]

private theorem symmetric_square_upper_triangular (S : Type) [CommRing S] (m : Matrix (Fin 2) (Fin 2) S) (h : m 1 0 = 0) :
    (∀ i j, j < i → symSquareMatrixHom S m i j = 0) ∧
      ∀ i, symSquareMatrixHom S m i i = ![m 0 0 ^ 2, m 0 0 * m 1 1, m 1 1 ^ 2] i := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [symSquareMatrixHom, h]
  · intro i
    fin_cases i <;> simp [symSquareMatrixHom, h]

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.ad0Facts :
    UpperTheory.V.Sd.Ad0Facts := by
  intro l _ Γ _ _ ρ
  have hd0 : ∀ g : GL (Fin 2) (Qbar l), (g : Matrix (Fin 2) (Fin 2) (Qbar l)).det ≠ 0 := fun g => g.det_ne_zero
  have hcp : ∀ s, (ad0 ρ s : Matrix (Fin 3) (Fin 3) (Qbar l)).charpoly =
      a0F (((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det)⁻¹ * (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace ^ 2 - 1) := fun s => by
    rw [adjoint_square_apply, adjoint_square_charpoly _ _ _ (inv_mul_cancel₀ (hd0 _))]
  refine ⟨fun h => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hA : Continuous fun g : GL (Fin 2) (Qbar l) =>
        ((g : Matrix (Fin 2) (Fin 2) (Qbar l)).det)⁻¹ • symSquareMatrixHom (Qbar l) (g : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
      (Units.continuous_val.matrix_det.inv₀ hd0).smul ((continuous_symmetric_square _).comp Units.continuous_val)
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact (hA.comp h).congr fun s => (adjoint_square_apply ρ s).symm
    · refine (hA.comp h.inv).congr fun s => ?_
      rw [← map_inv, adjoint_square_apply, map_inv]
      rfl
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 0, -2; 0, 1, 0; -2, 0, 0] (by simp [Matrix.det_fin_three]), ?_, fun s => ?_⟩
    · change (!![0, 0, -2; 0, 1, 0; -2, 0, 0] : Matrix (Fin 3) (Fin 3) (Qbar l))ᵀ = !![0, 0, -2; 0, 1, 0; -2, 0, 0]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · change _ * (!![0, 0, -2; 0, 1, 0; -2, 0, 0] : Matrix (Fin 3) (Fin 3) (Qbar l)) * _ = !![0, 0, -2; 0, 1, 0; -2, 0, 0]
      rw [adjoint_square_apply, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, symmetric_square_preserves_form, smul_smul, smul_smul,
        ← pow_two, ← mul_pow, inv_mul_cancel₀ (hd0 _), one_pow, one_smul]
  · rintro H a b ⟨g, hg⟩
    refine (shapeFacts l Γ 3 (ad0 ρ) 1).2.1 H ![a / b, 1, b / a] _ Fin.revPerm ⟨Units.map (symSquareMatrixHom _) g, fun s hs => ?_⟩ ?_
    · rw [adjoint_square_conjugate, hg s hs, symmetric_square_diagonal, ← Matrix.diagonal_smul, Matrix.det_diagonal]
      congr 1
      funext i
      fin_cases i <;> simp <;> field_simp
    · intro i s _
      fin_cases i <;> rfl
  · rintro H κ ⟨g, hg⟩
    refine ⟨Units.map (symSquareMatrixHom _) g, fun s => ?_⟩
    obtain ⟨h1, h2⟩ := hg s
    obtain ⟨k1, k2⟩ := symmetric_square_upper_triangular _ _ (h1 1 0 (by decide))
    rw [adjoint_square_conjugate]
    refine ⟨fun i j hij => by rw [Matrix.smul_apply, k1 i j hij, smul_zero], fun i => ?_⟩
    rw [Matrix.smul_apply, k2, Matrix.det_fin_two, h2 0, h2 1, h1 1 0 (by decide)]
    fin_cases i <;> simp <;> field_simp
  · intro s a b h
    obtain ⟨h1, h0⟩ := quadratic_charpoly_coeff_difference (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) a b
    rw [h, sub_self] at h1 h0
    rw [hcp, sub_eq_zero.mp (neg_eq_zero.mp h1.symm), sub_eq_zero.mp h0.symm, adjoint_charpoly_roots _ _ a.ne_zero b.ne_zero]
    simp
  · intro a b hab h s i
    obtain ⟨h1, h0⟩ := quadratic_charpoly_coeff_difference (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) (a s) (b s)
    have k1 := h s 1
    have k0 := h s 0
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at k1 k0
    rw [h1, norm_neg] at k1
    rw [h0] at k0
    have ht : Rl (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace ((a s : Qbar l) + b s) :=
      ⟨(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hab s).1.le (hab s).2.le), k1⟩
    have hn : ‖(a s : Qbar l) * b s‖ = 1 := by rw [norm_mul, (hab s).1, (hab s).2, one_mul]
    have hd : Rl (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).det ((a s : Qbar l) * b s) := ⟨hn.le, k0⟩
    have e := ((hd.inv hn).mul (ht.mul ht)).2
    rw [← pow_two, ← pow_two, ← sub_sub_sub_cancel_right _ _ 1] at e
    have := adjoint_charpoly_coeff_close e i
    rw [adjoint_charpoly_roots _ _ (a s).ne_zero (b s).ne_zero] at this
    rw [hcp]
    rw [Fin.prod_univ_three, mul_right_comm, mul_comm (X - C _) (X - C _), mul_right_comm]
    simpa using this
