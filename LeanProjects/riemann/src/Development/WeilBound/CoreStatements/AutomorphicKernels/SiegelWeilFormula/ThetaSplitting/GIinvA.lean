import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.ActUDiagMonomial

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.KSplit

namespace PositivityTheory.SiegelWeilFormula.KSplitA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem A_sym (d : SD σ) : ∃ ε : ℤˣ, ∀ i j, σ (d.A.J j i) = ((ε : ℤ) : E) * d.A.J i j := by
  rcases d.ok.sign with ⟨h, -⟩ | ⟨h, -⟩
  · exact ⟨1, fun i j => by rw [h.herm]; simp⟩
  · exact ⟨-1, fun i j => by rw [h.skew]; simp⟩

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
  have h2 : ((Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg, Matrix.det_one]
    simp
  intro h0
  apply h2
  rw [← h1, Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul]

theorem A_det (d : SD σ) : d.A.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have key : (d.A.J.map (d.B.emb w).1).det ≠ 0 := by
    rcases d.ok.sign with ⟨h, -⟩ | ⟨h, -⟩
    · exact det_ne_of_hasSig (h.sig w)
    · have := det_ne_of_hasSig (h.sig w)
      rw [Matrix.det_smul] at this
      exact right_ne_zero_of_mul this
  intro h0
  apply key
  rw [show d.A.J.map (d.B.emb w).1 = ((d.B.emb w).1 : E →+* ℂ).mapMatrix d.A.J from rfl, ← RingHom.map_det, h0, map_zero]

theorem mu_right (d : SD σ) : d.μ.IsMulRightInvariant := by
  obtain ⟨ε, hε⟩ := A_sym d
  exact (PositivityTheory.ThKF.unimodularity_holds F E σ d.cm d.m d.A.J ε hε (A_det d)).2.2 d.μ d.ok.haar

theorem fP_unitary {m n : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) (hu : u ∈ Matrix.unitaryGroup (Fin m) ℂ) (P : PX m n)
    (v : Matrix (Fin m) (Fin n) ℂ) : fP P (u * v) = fP (actU u P) v := by
  have key : ∀ i, (∑ a, ‖(u * v) a i‖ ^ 2 : ℝ) = ∑ a, ‖v a i‖ ^ 2 := by
    intro i
    have h1 : ∀ M : Matrix (Fin m) (Fin n) ℂ, ((∑ a, ‖M a i‖ ^ 2 : ℝ) : ℂ) = (Mᴴ * M) i i := by
      intro M
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Complex.conj_mul']
      rfl
    have h2 : (u * v)ᴴ * (u * v) = vᴴ * v := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ,
        ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').1 hu, Matrix.one_mul]
    exact_mod_cast (h1 (u * v)).trans ((congrArg (fun M => M i i) h2).trans (h1 v).symm)
  have hs : (∑ a, ∑ i, ‖(u * v) a i‖ ^ 2 : ℝ) = ∑ a, ∑ i, ‖v a i‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun a i => ‖v a i‖ ^ 2)]
    exact Finset.sum_congr rfl fun i _ => key i
  unfold fP
  rw [evX_actU]
  congr 1
  unfold gs
  rw [hs]

theorem mapStar_mul' {p q r : Type} [Fintype q] (A : Matrix p q ℂ) (B : Matrix q r ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j
  simp [Matrix.mul_apply]

theorem cw_mul' (d : SD σ) (w : InfinitePlace F) {p q r : Type} [Fintype q] (A : Matrix p q (AE F E))
    (B : Matrix q r (AE F E)) : d.cw w (A * B) = d.cw w A * d.cw w B :=
  Matrix.map_mul (f := piInf (d.B.emb w))

theorem cw_sub (d : SD σ) (w : InfinitePlace F) {p q : Type} (A B : Matrix p q (AE F E)) :
    d.cw w (A - B) = d.cw w A - d.cw w B := by
  ext i j
  simp [SD.cw]

theorem exists_embU (d : SD σ) (R : RD d) (w : InfinitePlace F) (u : Matrix (Fin d.m) (Fin d.m) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d.m) ℂ) : ∃ g : UA σ d.A.J, ∀ X : Mx F E d.m d.n,
      R.loc w (mat g⁻¹ * X) = (u * Matrix.of (R.loc w X) : Matrix (Fin d.m) (Fin d.n) ℂ) ∧
        (∀ w', w' ≠ w → d.cw w' (mat g⁻¹ * X - X) = 0) ∧ finOne F • (mat g⁻¹ * X - X) = 0 := by
  set fr : Matrix (Fin d.m) (Fin d.m) ℂ := (R.fr w).1 with hfr_def
  set fri : Matrix (Fin d.m) (Fin d.m) ℂ := ((R.fr w)⁻¹).1 with hfri_def
  have hb : fr * fri = 1 := by rw [hfr_def, hfri_def, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hb' : fri * fr = 1 := by rw [hfr_def, hfri_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have huu : u * uᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff).1 hu
  have huu' : uᴴ * u = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff').1 hu
  set h : Matrix (Fin d.m) (Fin d.m) ℂ := u.map star with hh_def
  have hhs : h.map star = u := by ext i j; simp [hh_def]
  have hht : hᵀ = uᴴ := by ext i j; simp [hh_def, Matrix.conjTranspose_apply]
  have h1 : h * uᵀ = 1 := by
    have : (u * uᴴ)ᵀ = h * uᵀ := by
      rw [Matrix.transpose_mul]; congr 1
    rw [← this, huu, Matrix.transpose_one]
  have h2 : uᵀ * h = 1 := by
    have : (uᴴ * u)ᵀ = uᵀ * h := by
      rw [Matrix.transpose_mul]; congr 1
    rw [← this, huu', Matrix.transpose_one]
  set Z := fr * h * fri with hZ_def
  set Z' := fr * uᵀ * fri with hZ'_def
  have hZZ : Z * Z' = 1 := by
    rw [hZ_def, hZ'_def, show fr * h * fri * (fr * uᵀ * fri) = fr * h * (fri * fr) * uᵀ * fri by
      simp only [Matrix.mul_assoc], hb', Matrix.mul_one, Matrix.mul_assoc fr h uᵀ, h1, Matrix.mul_one, hb]
  have hZZ' : Z' * Z = 1 := by
    rw [hZ_def, hZ'_def, show fr * uᵀ * fri * (fr * h * fri) = fr * uᵀ * (fri * fr) * h * fri by
      simp only [Matrix.mul_assoc], hb', Matrix.mul_one, Matrix.mul_assoc fr uᵀ h, h2, Matrix.mul_one, hb]
  have hζ0 : R.ζ ≠ 0 := by
    rcases R.hζ with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    · exact one_ne_zero
    · exact Complex.I_ne_zero
  set D : Matrix (Fin d.m) (Fin d.m) ℂ := d.A.J.map (d.B.emb w).1 with hD_def
  set Q : Matrix (Fin d.m) (Fin d.m) ℂ := frᵀ * D * fr.map star with hQ_def
  have hQ : R.ζ • Q = ((R.sg w : ℤ) : ℂ) • 1 := R.hfr w
  have hhQ : hᵀ * Q * h.map star = Q := by
    apply smul_right_injective _ hζ0
    show R.ζ • (hᵀ * Q * h.map star) = R.ζ • Q
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hQ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hhs, hht, huu']
  have hmem : (Krd.atM d w Z)ᵀ * incM F d.A.J * (Krd.atM d w Z).map (cA σ) = incM F d.A.J := by
    refine Place.cw_ext d (fun w' => ?_) ?_
    · rw [Krd.cw_mul, Krd.cw_mul, Place.cw_cA, Krd.cw_transpose, Krd.cw_incM, Krd.cw_atM]
      unfold Krd.fam
      split_ifs with hw
      · subst hw
        exact Krd.conj_unit fr fri h D Q hb rfl hhQ
      · rw [Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
    · have e1 : (finOne F • (1 : Matrix (Fin d.m) (Fin d.m) (AE F E))).map (cA σ) = finOne F • 1 := by
        rw [Krd.map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [Krd.fin_mul, Krd.fin_mul, ← Matrix.transpose_smul, Krd.fin_atM, ← Krd.map_cA_smul, Krd.fin_atM, e1,
        Matrix.transpose_smul, Matrix.transpose_one, ← Krd.fin_mul, ← Krd.fin_mul, Matrix.mul_one, Matrix.one_mul]
  let k : UA σ d.A.J := ⟨⟨Krd.atM d w Z, Krd.atM d w Z', by rw [← Krd.atM_mul, hZZ, Krd.atM_one],
    by rw [← Krd.atM_mul, hZZ', Krd.atM_one]⟩, hmem⟩
  refine ⟨k⁻¹, fun X => ⟨?_, fun w' hw' => ?_, ?_⟩⟩
  · rw [inv_inv]
    show (fri * d.cw w (Krd.atM d w Z * X)).map star = u * (fri * d.cw w X).map star
    rw [cw_mul', Krd.cw_atM]
    simp only [Krd.fam, if_true]
    rw [hZ_def, show fri * (fr * h * fri * d.cw w X) = (fri * fr) * h * (fri * d.cw w X) by
      simp only [Matrix.mul_assoc], hb', Matrix.one_mul, mapStar_mul', hhs]
  · rw [inv_inv]
    show d.cw w' (Krd.atM d w Z * X - X) = 0
    rw [cw_sub, cw_mul', Krd.cw_atM]
    simp only [Krd.fam, if_neg hw', Matrix.one_mul, sub_self]
  · rw [inv_inv]
    show finOne F • (Krd.atM d w Z * X - X) = 0
    rw [smul_sub, ← Matrix.smul_mul, Krd.fin_atM, Matrix.smul_mul, Matrix.one_mul, sub_self]

end PositivityTheory.SiegelWeilFormula.KSplitA

end
