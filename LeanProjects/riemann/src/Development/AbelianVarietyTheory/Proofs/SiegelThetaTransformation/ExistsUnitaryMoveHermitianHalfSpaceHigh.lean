import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsNearlyPrimitive
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryExt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsShortIso
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.Reduct

section Cplx
variable {N : ℕ}

theorem le_trace {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.PosSemidef) {T : ℝ}
    (hT : M.trace.re ≤ T) : ((T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - M).PosSemidef := by
  have hs := hM.1.spectral_theorem
  have ht := hM.1.trace_eq_sum_eigenvalues
  set U : Matrix (Fin N) (Fin N) ℂ := (hM.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hU
  have hUU : U * Uᴴ = 1 := (Unitary.coe_mul_star_self hM.1.eigenvectorUnitary)
  have hs' : M = U * diagonal (fun i => (hM.1.eigenvalues i : ℂ)) * Uᴴ := hs
  have e : (T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - M =
      U * diagonal (fun i => ((T - hM.1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have : diagonal (fun i => ((T - hM.1.eigenvalues i : ℝ) : ℂ)) =
        (T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - diagonal (fun i => (hM.1.eigenvalues i : ℂ)) := by
      ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, ← hs', Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hUU]
  rw [e]
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ U
  refine Matrix.PosSemidef.diagonal fun i => ?_
  have h1 : hM.1.eigenvalues i ≤ ∑ j, hM.1.eigenvalues j :=
    Finset.single_le_sum (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)
  have h2 : M.trace.re = ∑ j, hM.1.eigenvalues j := by
    rw [ht]; simp
  simp only [Pi.zero_apply]
  exact_mod_cast (by linarith : 0 ≤ T - hM.1.eigenvalues i)

theorem ge_of_inv_le {Y M : Matrix (Fin N) (Fin N) ℂ} (hY : Y.PosSemidef) (hM : Mᴴ = M)
    (h : Y * M = 1) {T : ℝ} (hT : 0 < T)
    (hle : ((T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - M).PosSemidef) :
    (Y - ((T⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by
  have h' : M * Y = 1 := mul_eq_one_comm.1 h
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have p1 := hY.conjTranspose_mul_mul_same (1 - ((T⁻¹ : ℝ) : ℂ) • M)
  have p2 := hle.smul (a := ((T⁻¹ ^ 2 : ℝ) : ℂ)) (by exact_mod_cast sq_nonneg T⁻¹)
  convert p1.add p2 using 1
  have hc : star ((T⁻¹ : ℝ) : ℂ) = ((T⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hM, hc]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, h, h', smul_sub, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring

theorem exists_maj {Z : Matrix (Fin N) (Fin N) ℂ} (hZ : (imH Z).PosDef) :
    let H := fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) * (imH Z)⁻¹ * (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ + I • Matrix.J (Fin N) ℂ
    H.PosDef ∧ H * (I • Matrix.J (Fin N) ℂ) * H = I • Matrix.J (Fin N) ℂ := by
  intro H
  set Y := imH Z with hY
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hZ.isUnit
  have h1 : Y * Y⁻¹ = 1 := mul_nonsing_inv _ hu
  have h2 : Y⁻¹ * Y = 1 := nonsing_inv_mul _ hu
  have hd : Z = Zᴴ + (2 * I) • Y := by
    rw [hY, imH, smul_smul, mul_inv_cancel₀ (by simp), one_smul]; abel
  have hJ : (I • Matrix.J (Fin N) ℂ) * (I • Matrix.J (Fin N) ℂ) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.J_squared]; simp
  have hP : (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ * (I • Matrix.J (Fin N) ℂ) * fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) = (-2 : ℂ) • Y := by
    rw [Matrix.mul_smul, Matrix.smul_mul, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.J, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, Matrix.mul_one, conjTranspose_one, zero_add, Matrix.one_mul,
      Matrix.mul_neg, add_zero]
    have : Z + -Zᴴ = (2 * I) • Y := by nth_rewrite 1 [hd]; abel
    rw [this, smul_smul]
    congr 1
    linear_combination 2 * I_mul_I
  have hH : H * (I • Matrix.J (Fin N) ℂ) * H = I • Matrix.J (Fin N) ℂ := by
    simp only [H]
    generalize I • Matrix.J (Fin N) ℂ = G at hJ hP ⊢
    generalize fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) = P at hP ⊢
    have e : P * Y⁻¹ * Pᴴ * G * (P * Y⁻¹ * Pᴴ) = (-2 : ℂ) • (P * Y⁻¹ * Pᴴ) := by
      calc _ = P * Y⁻¹ * (Pᴴ * G * P) * Y⁻¹ * Pᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hP, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc P, h2,
            Matrix.mul_one]
    generalize P * Y⁻¹ * Pᴴ = K at e
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, e, Matrix.mul_assoc, hJ, Matrix.one_mul,
      Matrix.mul_one]
    module
  have hK : fromRows Zᴴ (1 : Matrix (Fin N) (Fin N) ℂ) * Y⁻¹ * (fromRows Zᴴ (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ =
      fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ) * Y⁻¹ * (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ + (2 * I) • Matrix.J (Fin N) ℂ := by
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose,
      conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul Zᴴ _ Y⁻¹, fromRows_mul Z _ Y⁻¹,
      fromRows_mul_fromCols, fromRows_mul_fromCols, Matrix.J, fromBlocks_smul, fromBlocks_add,
      conjTranspose_conjTranspose, conjTranspose_one]
    generalize Zᴴ = W at hd
    rw [hd]
    congr 1 <;>
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, h1, h2, smul_zero, add_zero, smul_neg, add_neg_cancel_right, ← Matrix.mul_assoc Y]
  have hS : H.PosSemidef := by
    have p1 := hZ.inv.posSemidef.mul_mul_conjTranspose_same (fromRows Z (1 : Matrix (Fin N) (Fin N) ℂ))
    have p2 := hZ.inv.posSemidef.mul_mul_conjTranspose_same (fromRows Zᴴ (1 : Matrix (Fin N) (Fin N) ℂ))
    have p3 := (p1.add p2).smul (a := (2⁻¹ : ℂ)) (by positivity)
    rw [hK] at p3
    refine (congrArg Matrix.PosSemidef ?_).mp p3
    simp only [H]; module
  refine ⟨?_, hH⟩
  refine hS.posDef_iff_isUnit.2 ?_
  have : H * ((I • Matrix.J (Fin N) ℂ) * H * (I • Matrix.J (Fin N) ℂ)) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hH, hJ]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse this)

end Cplx

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem shortIso_all {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (N : ℕ) :
    ∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ N D 0 C := by
  induction N with
  | zero =>
    intro D _
    refine ⟨0, fun G H _ _ _ _ hW _ _ => ?_⟩
    obtain ⟨W, hW⟩ := hW
    exact ⟨W, fun i => i.elim0, hW, fun i => i.elim0⟩
  | succ N ih =>
    exact GlobalTheory.T.shortIsotropicVectorsExistence_succ_of_very_short_step E Ψ hΨ N ih fun D ε hD hε => GlobalTheory.SW.exists_shortIso E Ψ hΨ (N + 1) D ε hD hε

theorem exists_imag : ∃ (ξ : E) (D : ℕ), ξ ≠ 0 ∧ cc ξ = -ξ ∧ 0 < D ∧ IsIntegral ℤ ((D : E) * ξ) ∧
    IsIntegral ℤ ((D : E) * ξ⁻¹) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : E, cc x ≠ x := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ ({x - cc x, (x - cc x)⁻¹} : Finset E)
  have key : ∀ t : E, IsIntegral ℤ (y • t) → IsIntegral ℤ ((y.natAbs : E) * t) := fun t ht => by
    rw [zsmul_eq_mul] at ht
    rcases Int.natAbs_eq y with e | e
    · rw [e] at ht; simpa using ht
    · rw [e] at ht; simpa using ht.neg
  refine ⟨x - cc x, y.natAbs, sub_ne_zero.2 hx.symm, by simp [cc], Int.natAbs_pos.2 hy,
    key _ (h _ (by simp)), key _ (h _ (by simp))⟩

omit [IsCMField E] in
theorem den_smul_J {N D : ℕ} {t : E} (h : IsIntegral ℤ ((D : E) * t)) :
    Den D (t • Matrix.J (Fin N) E) := by
  rintro (i | i) (j | j) <;> by_cases hij : i = j <;>
    simp [Matrix.J, Matrix.one_apply, hij, isIntegral_zero, h, h.neg]

omit [NumberField E] [IsCMField E] in
theorem map_J {N : ℕ} (τ : E →+* ℂ) : (Matrix.J (Fin N) E).map τ = Matrix.J (Fin N) ℂ := by
  ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [Matrix.J, Matrix.one_apply, hij]

omit [NumberField E] [IsCMField E] in
theorem li_submatrix {k α β : Type} (e : α ≃ β) {W : Matrix k β E}
    (h : LinearIndependent E fun i => W i) :
    LinearIndependent E fun i => W.submatrix id e i :=
  h.map' (LinearEquiv.funCongrLeft E E e).toLinearMap (LinearEquiv.ker _)

omit [NumberField E] [IsCMField E] in
theorem hval_eq {Ψ : Finset (E →+* ℂ)} {k m : ℕ} (H : CM Ψ m m) (τ : Ψ)
    (W : Matrix (Fin k) (Fin m) E) (i : Fin k) :
    hval Ψ H τ (W i) = ((W.map τ.1 * H τ * (W.map τ.1)ᴴ) i i).re := by
  rw [Matrix.mul_assoc]; rfl

theorem exists_rows {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Z ∈ Hn Ψ N, ∃ W : Matrix (Fin N) (Fin N ⊕ Fin N) E, IntM W ∧
      LinearIndependent E (fun i => W i) ∧ W * Matrix.J (Fin N) E * ccT W = 0 ∧
      ∀ τ : Ψ, (W.map τ.1 * (fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ) * (imH (Z τ))⁻¹ *
        (fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ) * (W.map τ.1)ᴴ).trace.re ≤ B := by
  obtain ⟨ξ, D, hξ, hc, hD, hi, hi'⟩ := exists_imag (E := E)
  obtain ⟨C, hC⟩ := shortIso_all hΨ N D hD
  let e : Fin (2 * N) ≃ Fin N ⊕ Fin N := (finCongr (two_mul N)).trans finSumFinEquiv.symm
  have ht : ∀ τ : E →+* ℂ, τ ξ = ((τ ξ).im : ℂ) * I := fun τ => by
    have h1 := Base.map_cc τ ξ
    rw [hc, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp only [neg_re, conj_re] at h2
    apply Complex.ext <;> simp
    linarith
  have ht0 : ∀ τ : E →+* ℂ, (τ ξ).im ≠ 0 := fun τ h => by
    have := ht τ
    rw [h] at this
    exact hξ (by simpa using this)
  refine ⟨∑ τ : Ψ, N * (|C| / |(τ.1 ξ).im|), by positivity, fun Z hZ => ?_⟩
  have hGi : (ξ • Matrix.J (Fin N) E)⁻¹ = (-ξ⁻¹) • Matrix.J (Fin N) E := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.J_squared]
    simp [hξ]
  have hGm : ∀ τ : E →+* ℂ, (ξ • Matrix.J (Fin N) E).map τ =
      ((τ ξ).im : ℂ) • (I • Matrix.J (Fin N) ℂ) := fun τ => by
    rw [smul_smul, ← ht, ← map_J τ]
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  let H0 : Ψ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ := fun τ =>
    fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ) * (imH (Z τ))⁻¹ *
        (fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ))ᴴ + I • Matrix.J (Fin N) ℂ
  let H : CM Ψ (2 * N) (2 * N) := fun τ => (((|(τ.1 ξ).im| : ℝ) : ℂ) • H0 τ).submatrix e e
  have hmaj : IsMaj Ψ ((ξ • Matrix.J (Fin N) E).submatrix e e) H := fun τ => by
    obtain ⟨p1, p2⟩ : (H0 τ).PosDef ∧ H0 τ * (I • Matrix.J (Fin N) ℂ) * H0 τ = _ :=
      exists_maj (hZ τ)
    refine ⟨(p1.smul (by exact_mod_cast abs_pos.2 (ht0 τ.1))).submatrix e.injective, ?_⟩
    have h0 : ((τ.1 ξ).im : ℂ) ≠ 0 := by exact_mod_cast ht0 τ.1
    have hinv : (((τ.1 ξ).im : ℂ) • (I • Matrix.J (Fin N) ℂ))⁻¹ =
        ((τ.1 ξ).im : ℂ)⁻¹ • (I • Matrix.J (Fin N) ℂ) := by
      apply Matrix.inv_eq_right_inv
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.J_squared]
      have : ((τ.1 ξ).im : ℂ)⁻¹ * I * ((τ.1 ξ).im * I) = -1 := by
        field_simp; simp
      rw [this]; simp
    simp only [H]
    rw [← Matrix.submatrix_map, hGm, Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hinv]
    congr 1
    generalize I • Matrix.J (Fin N) ℂ = G at p2 ⊢
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, p2]
    congr 1
    have : ((|(τ.1 ξ).im| : ℝ) : ℂ) * ((|(τ.1 ξ).im| : ℝ) : ℂ) = (τ.1 ξ).im * (τ.1 ξ).im := by
      exact_mod_cast abs_mul_abs_self _
    field_simp
    linear_combination this
  have iso : ∀ W : Matrix (Fin N) (Fin N ⊕ Fin N) E,
      W.submatrix id e * (ξ • Matrix.J (Fin N) E).submatrix e e * ccT (W.submatrix id e) =
        ξ • (W * Matrix.J (Fin N) E * ccT W) := fun W => by
    have : ccT (W.submatrix id e) = (ccT W).submatrix e id := rfl
    rw [this, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.submatrix_id_id]
  refine Exists.elim (hC ((ξ • Matrix.J (Fin N) E).submatrix e e) H ?_ ?_ ?_ ?_ ?_ hmaj ?_) ?_
  rotate_right
  · rintro W ⟨w1, ⟨w2, w3⟩, w4⟩
    have hW : W = (W.submatrix id e.symm).submatrix id e := by ext i j; simp
    have hli := li_submatrix e.symm w2
    have hint : IntM (W.submatrix id e.symm) := fun i j => w1 _ _
    generalize W.submatrix id e.symm = V at hW hli hint
    subst hW
    rw [iso, smul_eq_zero] at w3
    have w5 := w3.resolve_left hξ
    refine ⟨V, hint, hli, w5, fun τ => ?_⟩
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ : Ψ => N * (|C| / |(τ.1 ξ).im|))
      (fun _ _ => by positivity) (Finset.mem_univ τ))
    have w6 := congrArg (fun X => X.map τ.1) w5
    simp only [Matrix.map_mul, Base.ccT_map, map_J, Matrix.map_zero _ (map_zero τ.1)] at w6
    rw [Matrix.trace, Complex.re_sum]
    refine (Finset.sum_le_card_nsmul _ _ (|C| / |(τ.1 ξ).im|) fun i _ => ?_).trans (by simp)
    have w7 := w4 i τ
    rw [hval_eq] at w7
    simp only [H, H0] at w7
    rw [← Matrix.submatrix_map, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, w6, smul_zero, add_zero,
      Matrix.smul_apply, smul_eq_mul, Complex.re_ofReal_mul] at w7
    rw [le_div_iff₀' (abs_pos.2 (ht0 τ.1))]
    exact w7.trans (le_abs_self C)
  · have : ccT (ξ • Matrix.J (Fin N) E) = cc ξ • ccT (Matrix.J (Fin N) E) := by
      ext i j; simp [ccT, cc]
    change (ccT (ξ • Matrix.J (Fin N) E)).submatrix e e = _
    rw [this, hc, Base.ccT_J]; simp
  · rw [Matrix.det_submatrix_equiv_self, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ) (Matrix.isUnit_det_J _ _).ne_zero
  · exact fun i j => den_smul_J hi _ _
  · rw [Matrix.inv_submatrix_equiv, hGi]
    exact fun i j => den_smul_J (by simpa using hi'.neg) _ _
  · refine ⟨(fromCols (0 : Matrix (Fin N) (Fin N) E) (1 : Matrix (Fin N) (Fin N) E)).submatrix id e,
      li_submatrix e ?_, ?_⟩
    · have : LinearIndependent E fun i : Fin N ⊕ Fin N => (1 : M2 E N) i :=
        Matrix.linearIndependent_rows_iff_isUnit.2 isUnit_one
      convert this.comp Sum.inr Sum.inr_injective using 1
      ext i (j | j) <;> simp [Matrix.one_apply]
    · rw [iso]
      convert smul_zero ξ
      ext i j
      simp [ccT, cc, Matrix.J, Matrix.mul_apply, Matrix.one_apply]
  · intro v _ _
    refine Finset.sum_nonneg fun τ _ => ?_
    have := (hmaj τ).1.posSemidef.dotProduct_mulVec_nonneg (star fun a => τ.1 (v a))
    rw [star_star] at this
    exact (Complex.nonneg_iff.1 this).1

end GlobalTheory.SW.Reduct

open GlobalTheory.SW.Reduct in

theorem GlobalTheory.SW.exists_move_high : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, ∃ (c : ℕ) (δ : ℝ), 0 < c ∧ 0 < δ ∧ ∀ Z ∈ Hn Ψ N, ∃ γ ∈ UU E N, Den c γ ∧ hAct Ψ γ Z ∈ HnGe Ψ N δ := by
  intro E _ _ _ Ψ hΨ N
  obtain ⟨B, hB0, hB⟩ := exists_rows hΨ N
  obtain ⟨c, C, hc, hprim⟩ := GlobalTheory.SW.exists_nearly_primitive E N
  obtain ⟨c', hc', hext⟩ := GlobalTheory.SW.RowExt.exists_unitary_ext E N c hc
  have hT : 0 < B * (N * (N * C ^ 2)) + 1 := by positivity
  refine ⟨c', (B * (N * (N * C ^ 2)) + 1)⁻¹, hc', inv_pos.2 hT, fun Z hZ => ?_⟩
  obtain ⟨W, w1, w2, w3, w4⟩ := hB Z hZ
  obtain ⟨a, a1, a2, a3, a4⟩ := hprim _ W w1 w2
  have hli : LinearIndependent E fun i => (a * W) i := by
    refine Matrix.vecMul_injective_iff.1 fun x y hxy => ?_
    simp only [← Matrix.vecMul_vecMul] at hxy
    exact Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det a).2 (Ne.isUnit a1))
      (Matrix.vecMul_injective_iff.2 w2 hxy)
  obtain ⟨γ, hγ, hden, hrow⟩ := hext (a * W) a3 hli (by
    rw [Base.ccT_mul, Matrix.mul_assoc a, Matrix.mul_assoc a, ← Matrix.mul_assoc _ (ccT W), w3]
    simp) a4
  refine ⟨γ, hγ, hden, fun τ => ?_⟩
  obtain ⟨h1, h2, -⟩ := (GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  obtain ⟨hQ, -, -, hI⟩ := h1 τ
  have hQe : hDen Ψ γ Z τ =
      a.map τ.1 * (W.map τ.1 * fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ)) := by
    have : fromCols (γ.toBlocks₂₁.map τ.1) (γ.toBlocks₂₂.map τ.1) = a.map τ.1 * W.map τ.1 := by
      rw [← Matrix.map_mul]
      ext i (j | j) <;> simp [← hrow, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]
    rw [← Matrix.mul_assoc, ← this, fromCols_mul_fromRows, Matrix.mul_one, hDen]
  have hY := hZ τ
  have hM := w4 τ
  have hY' := h2 τ
  rw [show ∀ (V : Matrix (Fin N) (Fin N ⊕ Fin N) ℂ) (P : Matrix (Fin N ⊕ Fin N) (Fin N) ℂ)
      (Y : Matrix (Fin N) (Fin N) ℂ), V * (P * Y * Pᴴ) * Vᴴ = V * P * Y * (V * P)ᴴ from
    fun V P Y => by simp only [conjTranspose_mul, Matrix.mul_assoc]] at hM
  have ha : ∀ i j, ‖a.map τ.1 i j‖ ≤ C := a2 τ.1
  generalize W.map τ.1 * fromRows (Z τ) (1 : Matrix (Fin N) (Fin N) ℂ) = R at hQe hM
  generalize a.map τ.1 = A at hQe ha
  generalize hDen Ψ γ Z τ = Q at hQ hI hQe
  generalize imH (hAct Ψ γ Z τ) = Y' at hI hY' ⊢
  generalize imH (Z τ) = Y at hI hY hM
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hY.isUnit
  have hinv : Y' * (Q * Y⁻¹ * Qᴴ) = 1 := by
    have e : Y⁻¹ * (Qᴴ * Y' * Q) = 1 := by rw [hI]; exact nonsing_inv_mul _ hu
    rw [← Matrix.mul_assoc] at e
    have e' := mul_eq_one_comm.1 e
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at e'
    exact mul_eq_one_comm.1 e'
  refine ge_of_inv_le hY'.posSemidef (hY.inv.posSemidef.mul_mul_conjTranspose_same Q).1 hinv hT ?_
  have p1 := (le_trace (hY.inv.posSemidef.mul_mul_conjTranspose_same R) hM).mul_mul_conjTranspose_same A
  have htr : (A * Aᴴ).trace.re ≤ N * (N * C ^ 2) := by
    rw [Matrix.trace, Complex.re_sum]
    refine (Finset.sum_le_card_nsmul _ _ (N * C ^ 2) fun i _ => ?_).trans (by simp)
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    refine (Finset.sum_le_card_nsmul _ _ (C ^ 2) fun j _ => ?_).trans (by simp)
    rw [conjTranspose_apply, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow,
      Complex.ofReal_re]
    exact pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2
  have p2 := (le_trace (posSemidef_self_mul_conjTranspose A) htr).smul (a := (B : ℂ))
    (by exact_mod_cast hB0)
  refine (congrArg Matrix.PosSemidef ?_).mp ((p1.add p2).add Matrix.PosSemidef.one)
  subst hQe
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    conjTranspose_mul, Matrix.mul_assoc]
  push_cast
  module
