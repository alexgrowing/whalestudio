import Formalism.LocalToGlobal.GlobalTheory.BlockActions.MapMemCSpanOfRat

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix

section Gen

theorem norm_detPow_sq {n : ℕ} (g : GL (Fin n) ℂ) (e : ℤ) :
    ‖detPow ℂ n g e‖ ^ 2 = ‖(g : Matrix (Fin n) (Fin n) ℂ).det‖ ^ (2 * e) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, norm_zpow, ← zpow_natCast, ← _root_.zpow_mul,
    mul_comm e]
  norm_num

theorem desc_scalar {K σ : Type} [Field K] (j : K →+* ℂ) (Q F : MvPolynomial σ K) (χ : ℂ) (k : ℕ) (hk : 0 < k)
    (hχ : χ ^ k = 1) (h : map j Q = χ⁻¹ • map j F) : ∃ a : K, Q = a • F ∧ ∀ s : K →+* ℂ, ‖s a‖ ≤ 1 := by
  have hinj : Function.Injective (map (σ := σ) j) := MvPolynomial.map_injective _ j.injective
  by_cases hF : F = 0
  · refine ⟨0, ?_, fun s => by simp⟩
    apply hinj
    rw [h, hF]
    simp
  · obtain ⟨m, hm⟩ : ∃ m, F.coeff m ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hF (MvPolynomial.ext _ _ fun m => by rw [hc m, coeff_zero])
    have hc : j (Q.coeff m) = χ⁻¹ * j (F.coeff m) := by
      have := congrArg (coeff m) h
      rwa [coeff_map, coeff_smul, coeff_map, smul_eq_mul] at this
    have hjm : j (F.coeff m) ≠ 0 := (map_ne_zero j).2 hm
    have ha : j (Q.coeff m / F.coeff m) = χ⁻¹ := by
      rw [map_div₀, hc, mul_div_assoc, div_self hjm, mul_one]
    refine ⟨Q.coeff m / F.coeff m, ?_, fun s => ?_⟩
    · apply hinj
      rw [h, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul F (Q.coeff m / F.coeff m), map_mul, map_C, ha]
    · have := norm_one_of_pow j s _ k hk (by rw [ha, inv_pow, hχ, inv_one])
      rw [this]

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem normal_form_agree {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.MainNotions.product_first_zeroth_parts.nfAll lam p p = Formalism.L2.Forms.nfAll lam p p := rfl

theorem norm_sqrtT_sq (d : ℤ) : ‖(((sqrtT D u) ^ d : ℂˣ) : ℂ)‖ ^ 2 = ((D.mem u).A.T : ℝ) ^ d := by
  have hT : (0 : ℝ) ≤ ((D.mem u).A.T : ℝ) := Nat.cast_nonneg _
  rw [Units.val_zpow_eq_zpow_val, norm_zpow]
  have h1 : ‖((sqrtT D u : ℂˣ) : ℂ)‖ = Real.sqrt ((D.mem u).A.T : ℝ) := by
    simp only [sqrtT, Units.val_mk0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [h1, ← zpow_natCast, ← _root_.zpow_mul, mul_comm d, _root_.zpow_mul, zpow_natCast, Real.sq_sqrt hT]

theorem chain_at (Tf : FormsTiedSym D u Ch chOf) (hBe : Formalism.L2.Ker.BeOnTie D u)
    (o' : D.what₂.Tau → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (ho' : ∀ τ, IsUnit (o' τ).det)
    (Y : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)
    (hY : Y ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m)) :
    (∏ τ, ‖(o' τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
        (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o' (Formalism.L2.Ker.brTen D u Y)) (subP o' (Formalism.L2.Ker.brTen D u Y))).re ≤
      ptB D u * ((∏ τ, ‖(dOT u (o' τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)) *
        (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (blkRow (fun τ => dOT u (o' τ)) Y)
          (blkRow (fun τ => dOT u (o' τ)) Y)).re) := by
  classical
  have hT : ∀ τ, IsUnit ((o' τ)ᵀ).det := fun τ => by rw [Matrix.det_transpose]; exact ho' τ
  let g : D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ := fun τ =>
    ⟨(o' τ)ᵀ, ((o' τ)ᵀ)⁻¹, Matrix.mul_nonsing_inv _ (hT τ), Matrix.nonsing_inv_mul _ (hT τ)⟩
  have hg : ∀ τ, ((g τ : GL _ ℂ) : Matrix _ _ ℂ) = (o' τ)ᵀ := fun τ => rfl
  have hL1 : blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (g τ))) Y =
      (∏ τ, detPow ℂ _ (gFull D u (g τ)) (lamTr D u τ).detShift) • blkRow (fun τ => dOT u (o' τ)) Y := by
    rw [blk_sqAct_eq]
    have e : (fun τ => ((gFull D u (g τ) : GL _ ℂ) : Matrix _ _ ℂ)ᵀ) = fun τ => dOT u (o' τ) :=
      funext fun τ => transpose_gFull_eq_dOT_of_eq_transpose (o' τ) (g τ) (hg τ)
    rw [e]
  have hR1 : blk (fun τ => sqAct ℂ _ (sgTr D u τ) (g τ)) (Formalism.L2.Ker.brTen D u Y) =
      (∏ τ, detPow ℂ _ (g τ) (sgTr D u τ).detShift) • subP o' (Formalism.L2.Ker.brTen D u Y) := by
    rw [blk_sqAct_eq]
    have e : (fun τ => ((g τ : GL _ ℂ) : Matrix _ _ ℂ)ᵀ) = o' := funext fun τ => by rw [hg, Matrix.transpose_transpose]
    rw [e]
    rfl
  have key := brTen_blk_gFull Tf g Y
  rw [hL1, hR1, map_smul, smul_smul] at key
  have hn := congrArg (fun p => (Formalism.L2.Forms.nfAll (D.fm u).sg p p).re) key
  simp only [nfAll_smul_reB, normal_form_agree] at hn
  have hdO : ∀ τ, IsUnit (dOT u (o' τ)).det := fun τ => by
    rw [det_dOT]
    exact (ho' τ).mul (Units.isUnit _)
  have hZ := blkRow_mem_CSpan ((D.fm u).lam D.R.m) (fun τ => dOT u (o' τ)) hdO Y hY
  have hle := nfAll_brTen_le' Tf hBe _ hZ

  have hshL : ∀ τ, (lamTr D u τ).detShift = shiftOf (lamT u D.R.m) τ := fun τ => by rw [shift_lamTr]
  have hshS : ∀ τ, (sgTr D u τ).detShift = shiftOf (sgT u) τ := fun τ => by
    have hI0 := interlaceTr D u (sg_interlace Tf.valP) τ
    have hS : (sgTr D u τ).detShift = (lamTr D u τ).detShift := Formalism.L2.Ker.sameShiftTr D u τ hI0
    rw [hS, hshL, shift_lamT_sgTS Tf τ]
  have hk1 : ‖∏ τ, detPow ℂ _ (gFull D u (g τ)) (lamTr D u τ).detShift‖ ^ 2 =
      ∏ τ, ‖(dOT u (o' τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ) := by
    rw [norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_detPow_sq, hshL, ← transpose_gFull_eq_dOT_of_eq_transpose (o' τ) (g τ) (hg τ), Matrix.det_transpose]
  have hk2 : ‖∏ τ, detPow ℂ _ (g τ) (sgTr D u τ).detShift‖ ^ 2 = ∏ τ, ‖(o' τ).det‖ ^ (2 * shiftOf (sgT u) τ) := by
    rw [norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_detPow_sq, hshS, hg, Matrix.det_transpose]
  have hcT : ‖∏ τ, (((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ)‖ ^ 2 = ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ) := by
    rw [norm_prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun τ _ => norm_sqrtT_sq _
  have hTpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hcpos : 0 < ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ) := Finset.prod_pos fun τ _ => zpow_pos hTpos _
  have hptB : ptB D u * ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ) = ∏ τ, (D.fm u).beOn τ ^ 2 := by
    unfold ptB
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [_root_.zpow_neg]
    field_simp
  rw [norm_mul, mul_pow, hk1, hk2, hcT] at hn
  set nW := (Formalism.L2.Forms.nfAll (D.fm u).sg (subP o' (Formalism.L2.Ker.brTen D u Y)) (subP o' (Formalism.L2.Ker.brTen D u Y))).re
  set nBZ := (Formalism.L2.Forms.nfAll (D.fm u).sg (Formalism.L2.Ker.brTen D u (blkRow (fun τ => dOT u (o' τ)) Y))
    (Formalism.L2.Ker.brTen D u (blkRow (fun τ => dOT u (o' τ)) Y))).re
  set nZ := (Formalism.L2.Forms.nfAll ((D.fm u).lam D.R.m) (blkRow (fun τ => dOT u (o' τ)) Y) (blkRow (fun τ => dOT u (o' τ)) Y)).re
  set K1 := ∏ τ, ‖(dOT u (o' τ)).det‖ ^ (2 * shiftOf (lamT u D.R.m) τ)
  set K2 := ∏ τ, ‖(o' τ).det‖ ^ (2 * shiftOf (sgT u) τ)
  set CT := ∏ τ, ((D.mem u).A.T : ℝ) ^ ((D.fm u).deg τ)
  set B := ∏ τ, (D.fm u).beOn τ ^ 2
  have hK1 : 0 ≤ K1 := Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _
  calc K2 * nW = (CT * K2 * nW) / CT := by field_simp
    _ = K1 * nBZ / CT := by rw [← hn]
    _ ≤ K1 * (B * nZ) / CT := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hK1) hcpos.le
    _ = ptB D u * (K1 * nZ) := by rw [← hptB]; field_simp

end Formalism.L2.GlobalTheoryTheory.Br
