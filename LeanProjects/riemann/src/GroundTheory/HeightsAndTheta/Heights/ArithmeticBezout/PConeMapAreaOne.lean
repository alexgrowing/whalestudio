import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMapAreaOne
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaFormulaInj
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFrameJacobianSum
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VolumePreservingUncurry
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal NNReal ComplexOrder

namespace ConeMapAreaFormula

def reImL (m : ℕ) : EuclideanSpace ℂ (Fin m) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin 2) where
  toFun y := WithLp.toLp 2 fun p => (![(y p.1).re, (y p.1).im] : Fin 2 → ℝ) p.2
  invFun w := WithLp.toLp 2 fun i => ⟨w (i, 0), w (i, 1)⟩
  map_add' y z := by
    ext p
    obtain ⟨i, k⟩ := p
    fin_cases k <;> simp
  map_smul' c y := by
    ext p
    obtain ⟨i, k⟩ := p
    fin_cases k <;> simp
  left_inv y := by
    ext i
    simp
  right_inv w := by
    ext p
    obtain ⟨i, k⟩ := p
    fin_cases k <;> simp

theorem reImL_apply (m : ℕ) (y : EuclideanSpace ℂ (Fin m)) (p : Fin m × Fin 2) :
    reImL m y p = (![(y p.1).re, (y p.1).im] : Fin 2 → ℝ) p.2 :=
  rfl

theorem norm_reImL (m : ℕ) (y : EuclideanSpace ℂ (Fin m)) : ‖reImL m y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [reImL_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply, sq, sq]

def reIm (m : ℕ) : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m × Fin 2) :=
  { reImL m with norm_map' := norm_reImL m }

theorem volume_preserving_uncurry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (Function.uncurry : (ι → κ → ℝ) → ι × κ → ℝ) volume volume :=
  _root_.UpperTheory.Reformulated.B.VolumePreservingUncurry.volume_preserving_uncurry ι κ

theorem measurePreserving_toLp (m : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : (Fin m → ℂ) → EuclideanSpace ℂ (Fin m)) volume volume := by
  have h1 : MeasurePreserving
      (fun (x : Fin m → ℂ) (i : Fin m) => Complex.measurableEquivPi (x i)) volume volume :=
    volume_preserving_pi fun _ => Complex.volume_preserving_equiv_pi
  have h2 := volume_preserving_uncurry (Fin m) (Fin 2)
  have h3 := PiLp.volume_preserving_toLp (Fin m × Fin 2)
  have h := (reIm m).symm.measurePreserving.comp (h3.comp (h2.comp h1))
  have hfun : (WithLp.toLp 2 : (Fin m → ℂ) → EuclideanSpace ℂ (Fin m)) =
      ⇑(reIm m).symm ∘ WithLp.toLp 2 ∘ Function.uncurry ∘
        fun x i => Complex.measurableEquivPi (x i) := by
    funext x
    rw [Function.comp_apply, LinearIsometryEquiv.eq_symm_apply]
    ext p
    obtain ⟨i, k⟩ := p
    fin_cases k <;> rfl
  rw [hfun]
  exact h

def splitE (e : ℕ) : EuclideanSpace ℂ (Fin (e + 1)) ≃ᵐ (Fin e → ℂ) × ℂ :=
  ((MeasurableEquiv.toLp 2 (Fin (e + 1) → ℂ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0)).trans MeasurableEquiv.prodComm

theorem splitE_apply (e : ℕ) (p : EuclideanSpace ℂ (Fin (e + 1))) :
    splitE e p = (fun j => p j.succ, p 0) := by
  ext j <;> simp [splitE, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm, Fin.tail]

theorem measurePreserving_splitE (e : ℕ) : MeasurePreserving (splitE e) volume volume := by
  have h1 := (measurePreserving_toLp (e + 1)).symm (MeasurableEquiv.toLp 2 (Fin (e + 1) → ℂ))
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (e + 1) => ℂ) 0
  have h3 := Measure.measurePreserving_swap (μ := (volume : Measure ℂ))
    (ν := (volume : Measure (Fin e → ℂ)))
  exact h3.comp (h2.comp h1)

def tailL (e : ℕ) : EuclideanSpace ℂ (Fin (e + 1)) →L[ℂ] (Fin e → ℂ) :=
  ContinuousLinearMap.pi fun j => EuclideanSpace.proj j.succ

theorem tailL_apply (e : ℕ) (p : EuclideanSpace ℂ (Fin (e + 1))) (j : Fin e) :
    tailL e p j = p j.succ :=
  rfl

def coneMapE {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (p : EuclideanSpace ℂ (Fin (e + 1))) :
    EuclideanSpace ℂ (Fin n) :=
  p 0 • WithLp.toLp 2 (v (tailL e p))

def gramVecs {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) : Fin (e + 1) → Fin n → ℂ :=
  Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)

theorem gramVol_eq {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    gramVol v y =
      (Matrix.det (Matrix.of fun a b => ∑ i, star (gramVecs v y a i) * gramVecs v y b i)).re :=
  rfl

theorem hasFDerivAt_coneMapE {e n : ℕ} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {p : EuclideanSpace ℂ (Fin (e + 1))} (hv : DifferentiableAt ℂ v (tailL e p)) :
    HasFDerivAt (coneMapE v)
      (p 0 • ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
          ((fderiv ℂ v (tailL e p)).comp (tailL e))) +
        (EuclideanSpace.proj (0 : Fin (e + 1)) :
          EuclideanSpace ℂ (Fin (e + 1)) →L[ℂ] ℂ).smulRight (WithLp.toLp 2 (v (tailL e p)))) p := by
  have hc := (EuclideanSpace.proj (0 : Fin (e + 1)) :
    EuclideanSpace ℂ (Fin (e + 1)) →L[ℂ] ℂ).hasFDerivAt (x := p)
  have hf := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.hasFDerivAt.comp p
    (hv.hasFDerivAt.comp p (tailL e).hasFDerivAt)
  exact hc.smul hf

theorem fderiv_coneMapE_single {e n : ℕ} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {p : EuclideanSpace ℂ (Fin (e + 1))} (hv : DifferentiableAt ℂ v (tailL e p)) (a : Fin (e + 1)) :
    fderiv ℂ (coneMapE v) p (EuclideanSpace.single a 1) =
      (Fin.cons 1 (fun _ => p 0) : Fin (e + 1) → ℂ) a • WithLp.toLp 2 (gramVecs v (tailL e p) a) := by
  rw [(hasFDerivAt_coneMapE hv).fderiv]
  refine Fin.cases ?_ (fun j => ?_) a
  · have h0 : tailL e (EuclideanSpace.single 0 1) = 0 := by
      funext j
      simp [tailL_apply, Fin.succ_ne_zero]
    simp [h0, gramVecs]
  · have h1 : tailL e (EuclideanSpace.single j.succ 1) = Pi.single j 1 := by
      funext i
      simp [tailL_apply, Pi.single_apply]
    simp [h1, gramVecs, Fin.succ_ne_zero]

theorem norm_eq_re_of_nonneg {z : ℂ} (hz : 0 ≤ z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 hz
  rw [← Complex.abs_re_eq_norm.2 h2.symm, abs_of_nonneg h1]

theorem areaJacobian_coneMapE {e n : ℕ} {v : (Fin e → ℂ) → (Fin n → ℂ)}
    {p : EuclideanSpace ℂ (Fin (e + 1))} (hv : DifferentiableAt ℂ v (tailL e p)) :
    areaJacobian ((fderiv ℂ (coneMapE v) p : EuclideanSpace ℂ (Fin (e + 1)) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) = ‖p 0‖ ^ (2 * e) * gramVol v (tailL e p) := by
  set S : EuclideanSpace ℂ (Fin (e + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    ↑(fderiv ℂ (coneMapE v) p)
  rw [FrameJacobianSumAlt.areaJacobian_restrictScalars, FrameJacobianSumAlt.det_adjoint_comp]
  obtain ⟨c, hcdef⟩ : ∃ c : Fin (e + 1) → ℂ, c = Fin.cons 1 (fun _ => p 0) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = gramVecs v (tailL e p) := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ,
      G = Matrix.of fun a b => ∑ i, star (w a i) * w b i := ⟨_, rfl⟩
  have hM : (Matrix.of fun i j : Fin (e + 1) => inner ℂ (S (EuclideanSpace.basisFun (Fin (e + 1)) ℂ i))
      (S (EuclideanSpace.basisFun (Fin (e + 1)) ℂ j))) =
      Matrix.diagonal (fun a => star (c a)) * G * Matrix.diagonal c := by
    ext a b
    simp only [S, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
      fderiv_coneMapE_single hv, inner_smul_left, inner_smul_right, Matrix.of_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal, hGdef, PiLp.inner_apply,
      RCLike.inner_apply, Complex.star_def, hcdef, hw]
    rw [Finset.sum_congr rfl fun x _ => mul_comm (gramVecs v (tailL e p) b x) _]
    ring
  have hG : G = Matrix.conjTranspose (Matrix.of fun i a => w a i) * Matrix.of fun i a => w a i := by
    ext a b
    simp [hGdef, Matrix.mul_apply]
  have hpsd : 0 ≤ G.det := by
    rw [hG]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg
  have hc : ∏ a, c a = p 0 ^ e := by
    simp [hcdef, Fin.prod_univ_succ]
  have hcs : ∏ a, star (c a) = star (p 0) ^ e := by
    simp [hcdef, Fin.prod_univ_succ]
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hc, hcs,
    norm_mul, norm_mul, norm_pow, norm_pow, norm_star, gramVol_eq, ← hw, ← hGdef, norm_eq_re_of_nonneg hpsd]
  ring

def coneIntegrand {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞)
    (q : (Fin e → ℂ) × ℂ) : ℝ≥0∞ :=
  F (q.2 • WithLp.toLp 2 (v q.1)) * ENNReal.ofReal (‖q.2‖ ^ (2 * e) * gramVol v q.1)

theorem lintegral_cone_prod {e : ℕ} {D : Set (Fin e → ℂ)} (G : (Fin e → ℂ) × ℂ → ℝ≥0∞)
    (hG : AEMeasurable G ((volume.restrict D).prod volume)) :
    ∫⁻ q in {q : (Fin e → ℂ) × ℂ | q.1 ∈ D ∧ q.2 ≠ 0}, G q = ∫⁻ x in D, ∫⁻ t, G (x, t) := by
  have hnull : (volume : Measure ((Fin e → ℂ) × ℂ)) (Set.univ ×ˢ {0}) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, mul_zero]
  have hset : {q : (Fin e → ℂ) × ℂ | q.1 ∈ D ∧ q.2 ≠ 0} = D ×ˢ Set.univ \ Set.univ ×ˢ {0} := by
    ext q
    simp
  rw [hset, setLIntegral_congr (sdiff_null_ae_eq_self hnull), Measure.volume_eq_prod,
    ← Measure.restrict_univ (μ := (volume : Measure ℂ)), ← Measure.prod_restrict]
  simp only [Measure.restrict_univ]
  exact lintegral_prod G hG

theorem aemeasurable_coneIntegrand {e n : ℕ} {U D : Set (Fin e → ℂ)}
    {v : (Fin e → ℂ) → (Fin n → ℂ)} {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hD : MeasurableSet D)
    (hDU : D ⊆ U) (hv : DifferentiableOn ℂ v U) (hF : Measurable F) :
    AEMeasurable (coneIntegrand v F) ((volume.restrict D).prod volume) := by
  have hvD : AEMeasurable v (volume.restrict D) := (hv.continuousOn.mono hDU).aemeasurable hD
  have hW : AEMeasurable (gramVecs v) (volume.restrict D) := by
    refine aemeasurable_pi_lambda _ fun a => ?_
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa [gramVecs] using hvD
    · simpa [gramVecs] using
        (measurable_fderiv_apply_const (𝕜 := ℂ) (f := v) (Pi.single j (1 : ℂ))).aemeasurable
  have hΦ : Continuous fun W : Fin (e + 1) → Fin n → ℂ =>
      (Matrix.det (Matrix.of fun a b => ∑ i, star (W a i) * W b i)).re := by
    refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.of_apply]
    refine continuous_finsetSum _ fun i _ => ?_
    fun_prop
  have hg : AEMeasurable (gramVol v) (volume.restrict D) := hΦ.measurable.comp_aemeasurable hW
  have h1 : AEMeasurable (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1))
      ((volume.restrict D).prod volume) :=
    measurable_snd.aemeasurable.smul
      ((PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable hvD).comp_fst
  refine (hF.comp_aemeasurable h1).mul ?_
  exact ((measurable_snd.norm.pow_const _).aemeasurable.mul hg.comp_fst).ennreal_ofReal

theorem hausdorff_eq_zero_of_lt {n d : ℕ} (h : n < d) :
    (Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) : Measure (EuclideanSpace ℂ (Fin n))) = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have hd : dimH (Set.univ : Set (EuclideanSpace ℂ (Fin n))) < (((2 * d : ℕ) : ℝ≥0) : ℝ≥0∞) := by
    rw [Real.dimH_univ_eq_finrank (EuclideanSpace ℂ (Fin n)), finrank_real_of_complex,
      finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 2 * n < 2 * d)
  simpa using hausdorffMeasure_of_dimH_lt hd

theorem volume_ball_E (e : ℕ) :
    volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) =
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) := by
  rw [InnerProductSpace.volume_ball_of_dim_even (k := e + 1)
    (by rw [finrank_real_of_complex, finrank_euclideanSpace_fin])]
  simp

theorem coordBall_eq (m k : ℕ) :
    {y : EuclideanSpace ℂ (Fin (m + k)) | ‖y‖ < 1 ∧ ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0} =
      zeroExt m k '' Metric.ball 0 1 := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image, Metric.mem_ball, dist_zero_right]
  constructor
  · rintro ⟨hy, hz⟩
    refine ⟨WithLp.toLp 2 fun i => y (Fin.castAdd k i), ?_, ?_⟩
    · rw [← norm_zeroExt m k]
      convert hy using 2
      ext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [zeroExt]
      · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
    · ext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [zeroExt]
      · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨by rwa [norm_zeroExt], fun j hj => ?_⟩
    revert hj
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · intro hi
      simp at hi
      omega
    · intro _
      simp [zeroExt]

end ConeMapAreaFormula

open ConeMapAreaFormula in

theorem ConeMapAreaOne.proof (hA : AreaFormulaInj.Statement) : ConeMapAreaOne.Statement := by
  intro n e U D v F hU hD hDU hv hinj hF
  by_cases hn : e + 1 ≤ n
  swap
  · rw [hausdorff_eq_zero_of_lt (by omega : n < e + 1)]
    simp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hfin : finrank ℝ (EuclideanSpace ℂ (Fin (e + 1))) = 2 * (e + 1) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  set S := {q : (Fin e → ℂ) × ℂ | q.1 ∈ D ∧ q.2 ≠ 0} with hSdef
  have hSm : MeasurableSet S := hD.prod (measurableSet_singleton (0 : ℂ)).compl
  set AE := splitE e ⁻¹' S with hAEdef
  have hAEm : MeasurableSet AE := (splitE e).measurable hSm
  set UE := {p : EuclideanSpace ℂ (Fin (e + 1)) | tailL e p ∈ U} with hUEdef
  have hUE : IsOpen UE := hU.preimage (tailL e).continuous
  have hAU : AE ⊆ UE := by
    intro p hp
    have h1 := hp.1
    rw [splitE_apply] at h1
    exact hDU h1
  have hdiff : ∀ p ∈ UE, DifferentiableAt ℂ v (tailL e p) := fun p hp =>
    hv.differentiableAt (hU.mem_nhds hp)

  have hvC : ContDiffOn ℂ 1 v U := by
    refine contDiffOn_pi.2 fun i => ?_
    have hvi : DifferentiableOn ℂ (fun x => v x i) U := fun x hx =>
      ((differentiableAt_pi.1 (hv.differentiableAt (hU.mem_nhds hx))) i).differentiableWithinAt
    exact (ReciprocityTheory.AnForm.Osgood.osgood e U _ hU hvi).contDiffOn (n := 1) hU.uniqueDiffOn
  have hC : ContDiffOn ℝ 1 (coneMapE (n := e + 1 + k) v) UE := by
    have h1 : ContDiffOn ℂ 1 (fun p => WithLp.toLp 2 (v (tailL e p)) :
        EuclideanSpace ℂ (Fin (e + 1)) → EuclideanSpace ℂ (Fin (e + 1 + k))) UE :=
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (e + 1 + k) => ℂ)).symm.contDiff.comp_contDiffOn
        (hvC.comp (tailL e).contDiff.contDiffOn (fun p hp => hp))
    exact ((EuclideanSpace.proj (0 : Fin (e + 1)) :
      EuclideanSpace ℂ (Fin (e + 1)) →L[ℂ] ℂ).contDiff.contDiffOn.smul h1).restrict_scalars ℝ
  have hcomp : coneMapE (n := e + 1 + k) v =
      (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) ∘ splitE e := by
    funext p
    rw [Function.comp_apply, splitE_apply]
    rfl
  have hinjE : Set.InjOn (coneMapE (n := e + 1 + k) v) AE := by
    rw [hcomp]
    exact hinj.comp (splitE e).injective.injOn (fun p hp => hp)
  have himg : coneMapE (n := e + 1 + k) v '' AE =
      (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) '' S := by
    rw [hcomp, Set.image_comp, Set.image_preimage_eq _ (splitE e).surjective]
  have key := hA (EuclideanSpace ℂ (Fin (e + 1))) (EuclideanSpace ℂ (Fin (e + 1 + k))) (2 * (e + 1))
    hfin UE AE (coneMapE v) F hUE hC hAU hAEm hinjE hF
  rw [himg] at key
  rw [key]
  have hJ : Set.EqOn (fun p => F (coneMapE v p) * ENNReal.ofReal (areaJacobian
      (fderiv ℝ (coneMapE (n := e + 1 + k) v) p : EuclideanSpace ℂ (Fin (e + 1)) →ₗ[ℝ]
        EuclideanSpace ℂ (Fin (e + 1 + k))))) (fun p => coneIntegrand v F (splitE e p)) AE := by
    intro p hp
    have hd := hdiff p (hAU hp)
    simp only
    rw [(hasFDerivAt_coneMapE hd).differentiableAt.fderiv_restrictScalars ℝ]
    rw [show ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ (coneMapE (n := e + 1 + k) v) p) :
        EuclideanSpace ℂ (Fin (e + 1)) →L[ℝ] EuclideanSpace ℂ (Fin (e + 1 + k))) :
          EuclideanSpace ℂ (Fin (e + 1)) →ₗ[ℝ] EuclideanSpace ℂ (Fin (e + 1 + k))) =
        ((fderiv ℂ (coneMapE (n := e + 1 + k) v) p : EuclideanSpace ℂ (Fin (e + 1)) →ₗ[ℂ]
          EuclideanSpace ℂ (Fin (e + 1 + k))).restrictScalars ℝ) from rfl]
    rw [areaJacobian_coneMapE hd, coneIntegrand, splitE_apply]
    rfl
  rw [setLIntegral_congr_fun hAEm hJ]
  have hexp : ((2 * (e + 1) : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin (e + 1))) : ℝ) := by
    rw [hfin]
  rw [coordBall_eq (e + 1) k, hexp, (isometry_zeroExt (e + 1) k).hausdorffMeasure_image
    (Or.inl (by positivity))]
  have hμ := Measure.isAddLeftInvariant_eq_smul
    (μH[(finrank ℝ (EuclideanSpace ℂ (Fin (e + 1))) : ℝ)] : Measure (EuclideanSpace ℂ (Fin (e + 1))))
    volume
  rw [hμ, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply,
    (measurePreserving_splitE e).setLIntegral_comp_preimage_emb (splitE e).measurableEmbedding,
    lintegral_cone_prod _ (aemeasurable_coneIntegrand hD hDU hv hF), volume_ball_E]
  simp only [ENNReal.smul_def, smul_eq_mul, coneIntegrand]
  ring

end GroundTheory.Heights₂.Heights
