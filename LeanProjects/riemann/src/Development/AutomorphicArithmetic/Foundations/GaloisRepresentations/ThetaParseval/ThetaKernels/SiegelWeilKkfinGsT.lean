import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.FirstFrameHalfEqMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinTDer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinKc

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem T_add_k (Φ Ψ : d.Fn) (X : Mx F E d.m d.n) : d.T (Φ + Ψ) X = d.T Φ X + d.T Ψ X := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, ← map_add]
  congr 1
  funext z
  exact mul_add _ _ _
variable (d) in
abbrev firstFrameColumns : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := incM F d.b.1.toCols₁
theorem split_k (u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    u = (u * (incM F (d.b⁻¹).1)ᵀ).toCols₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ + (u * (incM F (d.b⁻¹).1)ᵀ).toCols₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ := by
  have e : incM F d.b.1 = Matrix.fromCols (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d) (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns, _root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns, ← Matrix.fromCols_toCols d.b.1]; ext i (j | j) <;> rfl
  have e1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← incM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one,
      Matrix.transpose_one]
  calc u = u * (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ := by rw [Matrix.mul_assoc, e1, Matrix.mul_one]
    _ = _ := by
      rw [e, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols (u * (incM F (d.b⁻¹).1)ᵀ), Matrix.fromCols_mul_fromRows,
        Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
theorem firstColumns_eq_diag_mul : ∃ t : Matrix (Fin d.n) (Fin d.n) (AE F E), _root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d = _root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d * t := by
  obtain ⟨t, ht⟩ := d.ok.frame.2
  refine ⟨incM F t.1, ?_⟩
  have h2 : ∀ i j, d.b.1 i (Sum.inl j) = ∑ k, (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) i k * t.1 k j :=
    fun i j => congrFun₂ ht i j
  ext i j
  rw [Matrix.mul_apply]
  change inclR (AF F) (d.b.1 i (Sum.inl j)) = _
  rw [h2, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  congr 1
  rcases i with i | i <;>
  · change inclR (AF F) ((1 : Matrix (Fin d.n) (Fin d.n) E) i k) = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k
    by_cases h : i = k <;> simp [Matrix.one_apply, h]
def vacF_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, gs (2 * Real.pi) (R.loc w X)) * g fun k => (d.crd X k).2
theorem cw_add_smul_k (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (t : ℝ) :
    d.cw w (X + realAd F t • Z) = d.cw w X + (t : ℂ) • d.cw w Z := by
  ext i j
  show piInf (d.B.emb w) ((X + realAd F t • Z) i j) = piInf (d.B.emb w) (X i j) + (t : ℂ) * piInf (d.B.emb w) (Z i j)
  rw [Matrix.add_apply, Matrix.smul_apply, map_add, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul]
theorem crd_add_smul_snd_k (X Z : Mx F E d.m d.n) (t : ℝ) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd (X + realAd F t • Z) k).2 = (d.crd X k).2 := by
  have e : d.crd (X + realAd F t • Z) k = d.crd X k + realAd F t * d.crd Z k := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.add_apply, Matrix.smul_apply, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
  rw [e, snd_add_realAd]
def qL_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X Z : Mx F E d.m d.n) (t : ℝ) : ℝ :=
  ∑ w, ∑ a, ∑ i, ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2
theorem gs_loc_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (t : ℝ) :
    gs (2 * Real.pi) (R.loc w (X + realAd F t • Z)) = Complex.exp ((-(2 * Real.pi * ∑ a, ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) : ℝ) : ℂ) := by
  simp only [gs, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, _root_.PositivityTheory.SiegelWeilFormula.KK.cw_add_smul_k, Matrix.mul_add, Matrix.mul_smul, Matrix.map_apply, norm_star, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_neg]
theorem vacF_line_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X Z : Mx F E d.m d.n) (t : ℝ) :
    _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g (X + realAd F t • Z) = Complex.exp ((-(2 * Real.pi) * _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z t : ℝ) : ℂ) * g fun k => (d.crd X k).2 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, _root_.PositivityTheory.SiegelWeilFormula.KK.crd_add_smul_snd_k, _root_.PositivityTheory.SiegelWeilFormula.KK.gs_loc_k]
  congr 1
  rw [← Complex.exp_sum]
  congr 1
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.qL_k]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
theorem vacF_deriv_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X Z : Mx F E d.m d.n) :
    HasDerivAt (fun t : ℝ => _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g (X + realAd F t • Z))
      (((-(4 * Real.pi) * ∑ w, (Matrix.trace ((((R.fr w)⁻¹).1 * d.cw w X)ᴴ * (((R.fr w)⁻¹).1 * d.cw w Z))).re : ℝ) : ℂ) *
        _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X) 0 := by
  have hf : (fun t : ℝ => _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g (X + realAd F t • Z)) =
      fun t => Complex.exp ((-(2 * Real.pi) * _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z t : ℝ) : ℂ) * g fun k => (d.crd X k).2 :=
    funext (_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_line_k R g X Z)
  rw [hf]
  have hq : HasDerivAt (_root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z)
      (∑ w, ∑ a, ∑ i, 2 * (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re) 0 := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k
    refine HasDerivAt.fun_sum (A := fun w (t : ℝ) => ∑ a, ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun w _ => ?_
    refine HasDerivAt.fun_sum (A := fun a (t : ℝ) => ∑ i,
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun a _ => ?_
    exact HasDerivAt.fun_sum (A := fun i (t : ℝ) =>
      ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2) fun i _ =>
      hasDerivAt_normSq _ _
  have he := ((hq.const_mul (-(2 * Real.pi))).ofReal_comp.cexp).mul_const (g fun k => (d.crd X k).2)
  refine he.congr_deriv ?_
  have e0 : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X = Complex.exp ((-(2 * Real.pi) * _root_.PositivityTheory.SiegelWeilFormula.KK.qL_k R X Z 0 : ℝ) : ℂ) * g fun k => (d.crd X k).2 := by
    have := _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_line_k R g X Z 0
    rwa [realAd_zero, zero_smul, add_zero] at this
  rw [e0]
  have e2 : (∑ w, ∑ a, ∑ i, 2 * (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re) =
      2 * ∑ w, ∑ a, ∑ i, (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re := by
    simp only [Finset.mul_sum]
  simp only [trace_re, e2]
  push_cast
  ring
theorem frame_form_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) :
    (d.b.1.map (d.B.emb w).1)ᵀ * dbl (d.Y.J.map (d.B.emb w).1) * (d.b.1.map (d.B.emb w).1).map star = jE d.n R.ε := by
  have h := d.ok.good.cm
  have cst : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E, (x.map σ).map (d.B.emb w).1 =
      (x.map (d.B.emb w).1).map star := fun x => by
    ext i j; exact h.2.2.2 (d.B.emb w).1 (x i j)
  have hd : (dbl d.Y.J).map (d.B.emb w).1 = dbl (d.Y.J.map (d.B.emb w).1) := by
    ext (i | i) (j | j) <;> simp [dbl, Matrix.fromBlocks]
  have := congrArg (fun x => x.map (d.B.emb w).1) R.hε
  simp only [Matrix.map_mul, Matrix.transpose_map, cst, hd] at this
  rw [this]
  ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [jE, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, hij]
theorem map_mul_incM_T_k {p q r : Type} [Fintype q] (w : InfinitePlace F) (x : Matrix p q (AE F E)) (y : Matrix r q E) :
    (x * (incM F y)ᵀ).map (piInf (d.B.emb w)) = x.map (piInf (d.B.emb w)) * (y.map (d.B.emb w).1)ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_map, map_incM']
theorem T_D_vac_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch)
    (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g) {u : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u) (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e u) Φ) X = (∑ w, Sw (d.A.J.map (d.B.emb w).1) ((R.fr w)⁻¹).1 (dbl (d.Y.J.map (d.B.emb w).1))
      (d.b.1.map (d.B.emb w).1) ((d.b⁻¹).1.map (d.B.emb w).1) (d.cw w X) (d.cw w u)) * _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X := by
  obtain ⟨tA, htA⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.firstColumns_eq_diag_mul (d := d)
  set W := u * (incM F (d.b⁻¹).1)ᵀ with hW
  have hWa : At (evI F) W := at_mul hu _
  have h1 : At (evI F) (W.toCols₁ * tAᵀ) := at_mul (at_toCols₁ hWa) _
  have h2 : At (evI F) W.toCols₂ := at_toCols₂ hWa
  have e1 : W.toCols₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ = (W.toCols₁ * tAᵀ) * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ := by
    rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]
  have hs := _root_.PositivityTheory.SiegelWeilFormula.KK.split_k u
  rw [← hW, e1] at hs
  have hsplitD : Box.D (d.dd.e u) Φ = Box.D (d.dd.e ((W.toCols₁ * tAᵀ) * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ +
      Box.D (d.dd.e (W.toCols₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ)) Φ := by
    conv_lhs => rw [hs]
    rw [map_add, Box.D_add_left]
  rw [hsplitD, _root_.PositivityTheory.SiegelWeilFormula.KK.T_add_k, _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k hΦ h1, hT]
  have hder := _root_.PositivityTheory.SiegelWeilFormula.KK.hasDerivAt_translate_secondColumns hΦ h2 X
  rw [hT] at hder
  rw [(_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_deriv_k R g X W.toCols₂).unique hder |>.symm]
  have hmX : ∀ w, (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ := fun w => by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]; rfl
  have hmW : ∀ w, W.map (piInf (d.B.emb w)) = d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ := fun w => by
    rw [hW, _root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]; rfl
  have hmW1 : ∀ w, (W.toCols₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ).map (piInf (d.B.emb w)) =
      (d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₁ * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ := fun w => by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k, ← hmW]; rfl
  have hmW2 : ∀ w, d.cw w W.toCols₂ = (d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₂ := fun w => by
    rw [← hmW]; rfl
  have hm : _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d (W.toCols₁ * tAᵀ) X = ∑ w, -(2 * (T1 (d.A.J.map (d.B.emb w).1) (dbl (d.Y.J.map (d.B.emb w).1))
      (d.b.1.map (d.B.emb w).1) (d.cw w X) ((d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₁)).re) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k, ← e1, _root_.PositivityTheory.SiegelWeilFormula.KK.trace_sp_k]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hmX w, hmW1 w]
    rfl
  rw [hm]
  simp only [hmW2, Sw, T2]
  rw [Finset.sum_mul]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
theorem vac_rel_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch)
    (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g) {u u' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)} (hu : At (evI F) u)
    (hu' : At (evI F) u') (hr : Box.Rel d.B.emb (fun _ => 1) (_root_.PositivityTheory.SiegelWeilFormula.KK.thA_k R) (_root_.PositivityTheory.SiegelWeilFormula.KK.thB_k d R.ε) u u') (X : Mx F E d.m d.n) :
    d.T (Box.D (d.dd.e u') Φ) X = Complex.I * d.T (Box.D (d.dd.e u) Φ) X := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_vac_k R g hΦ hT hu' X, _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_vac_k R g hΦ hT hu X, ← mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have e2 : (d.b⁻¹).1.map (d.B.emb w).1 * d.b.1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hfi : (R.fr w).1 * ((R.fr w)⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Sw_rel e2 hfi (_root_.PositivityTheory.SiegelWeilFormula.KK.frame_form_k R w) (R.hfr w) R.hζ (d.cw w X) (d.cw w u) (d.cw w u') (hr w)
end PositivityTheory.SiegelWeilFormula.KK
end
end
