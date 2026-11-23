import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEPairAtDeriv

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section Sob

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem hsVecR_dSl (U V : Wq →L[ℂ] Wp) :
    (hsVecR (Wp := Wp) (Wq := Wq)).comp (dSl U V) = Complex.reCLM.smulRight (hsVecR (U + V)) +
      Complex.imCLM.smulRight (hsVecR (Complex.I • (U - V))) := by
  refine ContinuousLinearMap.ext fun h => ?_
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, h = x + y * Complex.I := ⟨h.re, h.im, (Complex.re_add_im h).symm⟩
  simp only [ContinuousLinearMap.comp_apply, dSl_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.imCLM_apply, hsVecR_apply, hsVec_add',
    hsVec_smul']
  have hs : B.hsVec (U - V) = B.hsVec U - B.hsVec V := by
    rw [sub_eq_add_neg, hsVec_add', ← neg_one_smul ℂ V, hsVec_smul', neg_one_smul, sub_eq_add_neg]
  rw [hs]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
  simp only [mul_zero, mul_one, sub_zero, zero_add, add_zero, zero_sub]
  rw [← Complex.coe_smul, ← Complex.coe_smul]
  module

def Dx (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') : RadSp k r z z' π π' :=
  dT X l Ξ + dTb X l Ξ

def Dy (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') : RadSp k r z z' π π' :=
  Complex.I • (dT X l Ξ - dTb X l Ξ)

theorem sl_hasFDerivAt (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') (y : Fin r → ℂ)
    (g : Mx k r) {s : ℂ} (hs : s ≠ 0) :
    HasFDerivAt (fun s' => hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s') g))
      (Complex.reCLM.smulRight (hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)) +
        Complex.imCLM.smulRight (hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g))) s := by
  have h := hsVecR.hasFDerivAt.comp s (slice_hasFDerivAt X l Ξ y g hs)
  rw [hsVecR_dSl] at h
  simpa only [Dx, Dy, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, Function.comp_def] using h

theorem sq_add_le_two {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 := norm_add_le a b
  have h2 := norm_nonneg (a + b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem sq_sub_le_two {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := sq_add_le_two a (-b)
  rwa [← sub_eq_add_neg, norm_neg] at this

def wd7 (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') : Fin 7 → RadSp k r z z' π π' :=
  ![Ξ, dT X l Ξ, dTb X l Ξ, dT X l (dT X l Ξ), dTb X l (dT X l Ξ), dT X l (dTb X l Ξ), dTb X l (dTb X l Ξ)]

theorem hsVecR_Ismul (A : Wq →L[ℂ] Wp) : ‖hsVecR (Complex.I • A)‖ = ‖hsVecR A‖ := by
  rw [hsVecR_apply, hsVecR_apply, hsVec_smul', norm_smul, Complex.norm_I, one_mul]

theorem four_le_seven (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') (p : Fin r → ℂ)
    (g : Mx k r) :
    ‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) p g)‖ ^ 2 + ‖hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) p g)‖ ^ 2 +
      ‖hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) p g)‖ ^ 2 +
      ‖hsVecR ((Dx X l (Dy X l Ξ) : Fn k r (Wq →L[ℂ] Wp)) p g)‖ ^ 2 ≤
    4 * ∑ i, ‖hsVecR ((wd7 X l Ξ i : Fn k r (Wq →L[ℂ] Wp)) p g)‖ ^ 2 := by
  set a := fun Ψ : RadSp k r z z' π π' => hsVecR ((Ψ : Fn k r (Wq →L[ℂ] Wp)) p g) with ha
  have eA : ∀ Ψ Ψ' : RadSp k r z z' π π', a (Ψ + Ψ') = a Ψ + a Ψ' := fun Ψ Ψ' => by
    simp only [ha, Submodule.coe_add, Pi.add_apply, map_add]
  have eS : ∀ Ψ Ψ' : RadSp k r z z' π π', a (Ψ - Ψ') = a Ψ - a Ψ' := fun Ψ Ψ' => by
    simp only [ha, Submodule.coe_sub, Pi.sub_apply, map_sub]
  have eI : ∀ Ψ : RadSp k r z z' π π', ‖a (Complex.I • Ψ)‖ = ‖a Ψ‖ := fun Ψ => by
    simp only [ha, Submodule.coe_smul, Pi.smul_apply]
    exact hsVecR_Ismul _
  have hx : ‖a (Dx X l Ξ)‖ ^ 2 ≤ 2 * ‖a (dT X l Ξ)‖ ^ 2 + 2 * ‖a (dTb X l Ξ)‖ ^ 2 := by
    rw [Dx, eA]; exact sq_add_le_two _ _
  have hy : ‖a (Dy X l Ξ)‖ ^ 2 ≤ 2 * ‖a (dT X l Ξ)‖ ^ 2 + 2 * ‖a (dTb X l Ξ)‖ ^ 2 := by
    rw [Dy, eI, eS]; exact sq_sub_le_two _ _
  have exy : Dx X l (Dy X l Ξ) = Complex.I • (dT X l (dT X l Ξ) - dT X l (dTb X l Ξ)) +
      Complex.I • (dTb X l (dT X l Ξ) - dTb X l (dTb X l Ξ)) := by
    simp only [Dx, Dy, map_smul, map_sub]
  have hxy : ‖a (Dx X l (Dy X l Ξ))‖ ^ 2 ≤ 4 * ‖a (dT X l (dT X l Ξ))‖ ^ 2 + 4 * ‖a (dT X l (dTb X l Ξ))‖ ^ 2 +
      4 * ‖a (dTb X l (dT X l Ξ))‖ ^ 2 + 4 * ‖a (dTb X l (dTb X l Ξ))‖ ^ 2 := by
    rw [exy, eA]
    refine (sq_add_le_two _ _).trans ?_
    rw [eI, eI, eS, eS]
    nlinarith [sq_sub_le_two (a (dT X l (dT X l Ξ))) (a (dT X l (dTb X l Ξ))),
      sq_sub_le_two (a (dTb X l (dT X l Ξ))) (a (dTb X l (dTb X l Ξ)))]
  simp only [Fin.sum_univ_seven, wd7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
  show ‖a Ξ‖ ^ 2 + ‖a (Dx X l Ξ)‖ ^ 2 + ‖a (Dy X l Ξ)‖ ^ 2 + ‖a (Dx X l (Dy X l Ξ))‖ ^ 2 ≤ _
  simp only [Matrix.cons_val]
  nlinarith [sq_nonneg ‖a Ξ‖, sq_nonneg ‖a (dT X l Ξ)‖, sq_nonneg ‖a (dTb X l Ξ)‖]

end Sob

section Dom

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem dT_lc (X : ActualOps k r z z' π π') (l : Fin r) {Ξ : RadSp k r z z' π π'} (h : Ξ ∈ lcSub k r z z' π π') :
    dT X l Ξ ∈ lcSub k r z z' π π' := by
  simp only [dT, Module.End.mul_apply]; exact op_lc X l 2 _ (op_lc X l 0 _ h)

theorem dTb_lc (X : ActualOps k r z z' π π') (l : Fin r) {Ξ : RadSp k r z z' π π'} (h : Ξ ∈ lcSub k r z z' π π') :
    dTb X l Ξ ∈ lcSub k r z z' π π' := by
  simp only [dTb, Module.End.mul_apply]; exact op_lc X l 5 _ (op_lc X l 3 _ h)

theorem seven_derivatives_preserve_compact (X : ActualOps k r z z' π π') (l : Fin r) {Ξ : RadSp k r z z' π π'} (h : Ξ ∈ lcSub k r z z' π π')
    (i : Fin 7) : wd7 X l Ξ i ∈ lcSub k r z z' π π' := by
  fin_cases i <;>
    first
    | exact h
    | exact dT_lc X l h
    | exact dTb_lc X l h
    | exact dT_lc X l (dT_lc X l h)
    | exact dTb_lc X l (dT_lc X l h)
    | exact dT_lc X l (dTb_lc X l h)
    | exact dTb_lc X l (dTb_lc X l h)

theorem pairAt_self_real (μ : Measure (Mt k r)) (Ξ : RadSp k r z z' π π') (p : Fin r → ℂ) :
    pairAt μ Ξ Ξ p = ((‖pairAt μ Ξ Ξ p‖ : ℝ) : ℂ) := by
  have e : pairAt μ Ξ Ξ p = ((∫ x : Mt k r, ‖B.hsVec ((Ξ : Fn k r (Wq →L[ℂ] Wp)) p (Matrix.of x))‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    unfold pairAt
    simp_rw [hsInner_self_ofRealI]
    exact integral_complex_ofReal
  rw [e, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => by positivity)]

theorem wtI_real (i : Fin (r + 1)) (c' : Cf r i) : wtI i c' = ((‖wtI i c'‖ : ℝ) : ℂ) := by
  unfold wtI
  rw [Complex.norm_real, Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]

theorem norm_fs_self (μ : Measure (Mt k r)) (l : Fin r) (Ξ : RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    ‖fs μ l Ξ Ξ c t‖ = ∫ c' : Cf r l.succ, ‖wtI l.succ c' * pairAt μ Ξ Ξ (glue l.succ (Function.update c l t) c')‖ := by
  unfold fs
  have e : (fun c' : Cf r l.succ => wtI l.succ c' * pairAt μ Ξ Ξ (glue l.succ (Function.update c l t) c')) =
      fun c' => ((‖wtI l.succ c' * pairAt μ Ξ Ξ (glue l.succ (Function.update c l t) c')‖ : ℝ) : ℂ) := by
    funext c'
    rw [norm_mul, Complex.ofReal_mul, ← wtI_real, ← pairAt_self_real]
  rw [e, integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]

theorem norm_hsInner_self (A : Wq →L[ℂ] Wp) : ‖B.hsInner A A‖ = ‖hsVecR A‖ ^ 2 := by
  rw [hsInner_self_ofRealI, Complex.norm_real, Real.norm_of_nonneg (by positivity), hsVecR_apply]

theorem pt_sob (hS : JSSob2) (t0 : ℂ) (δ : ℝ) (hδ : 0 < δ) (hB : ∀ s ∈ Metric.closedBall t0 (2 * δ), s ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X : ActualOps k r z z' π π') (l : Fin r) (Ξ : RadSp k r z z' π π') (y : Fin r → ℂ)
      (g : Mx k r), ∀ t ∈ Metric.ball t0 δ, ‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) g)‖ ^ 2 ≤
        K * ∫ s in Metric.closedBall t0 (2 * δ),
          4 * ∑ i, ‖hsVecR ((wd7 X l Ξ i : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 := by
  obtain ⟨K, hK⟩ := hS t0 δ hδ
  refine ⟨|K|, abs_nonneg _, fun X l Ξ y g t ht => ?_⟩
  have slc : ∀ Ψ : RadSp k r z z' π π', ContinuousOn
      (fun s => ‖hsVecR ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2)
      (Metric.closedBall t0 (2 * δ)) := fun Ψ s hs =>
    ((sl_hasFDerivAt X l Ψ y g (hB s hs)).continuousAt.norm.pow 2).continuousWithinAt
  have key := hK (PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp))
    (fun s => hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g))
    (fun s => hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g))
    (fun s => hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g))
    (fun s => hsVecR ((Dx X l (Dy X l Ξ) : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g))
    (fun s hs => sl_hasFDerivAt X l Ξ y g (hB s hs))
    (fun s hs => ⟨_, sl_hasFDerivAt X l (Dy X l Ξ) y g (hB s hs)⟩)
    (fun s hs => (sl_hasFDerivAt X l (Dx X l Ξ) y g (hB s hs)).continuousAt.continuousWithinAt)
    (fun s hs => (sl_hasFDerivAt X l (Dx X l (Dy X l Ξ)) y g (hB s hs)).continuousAt.continuousWithinAt) t ht
  refine key.trans ?_
  have hI4 : IntegrableOn (fun s => ‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
      ‖hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
      ‖hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
      ‖hsVecR ((Dx X l (Dy X l Ξ) : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2)
      (Metric.closedBall t0 (2 * δ)) :=
    ((((slc Ξ).add (slc _)).add (slc _)).add (slc _)).integrableOn_compact (isCompact_closedBall _ _)
  have hI7 : IntegrableOn (fun s => 4 * ∑ i, ‖hsVecR ((wd7 X l Ξ i : Fn k r (Wq →L[ℂ] Wp))
      (Function.update y l s) g)‖ ^ 2) (Metric.closedBall t0 (2 * δ)) :=
    (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => slc _)).integrableOn_compact
      (isCompact_closedBall _ _)
  calc K * ∫ s in Metric.closedBall t0 (2 * δ), (‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dx X l (Dy X l Ξ) : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2)
      ≤ |K| * ∫ s in Metric.closedBall t0 (2 * δ), (‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dx X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dy X l Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2 +
        ‖hsVecR ((Dx X l (Dy X l Ξ) : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (setIntegral_nonneg measurableSet_closedBall fun s _ => by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_mono_on hI4 hI7 measurableSet_closedBall
        fun s _ => four_le_seven X l Ξ _ g) (abs_nonneg K)

end Dom

section Main

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem slDom_of_loc (hS : JSSob2) (hM : JSMeas) (X : ActualOps k r z z' π π') (μ : Measure (Mt k r))
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r) (c : Fin r → ℂ) (Φ : RadSp k r z z' π π')
    (hΦ : Φ ∈ lcSub k r z z' π π') (t0 : ℂ) (ht0 : t0 ≠ 0)
    (hloc : ∀ i : Fin 7, ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε,
      LevelSquareIntegrable μ l.succ (wd7 X l Φ i) (Function.update c l t) ∧ ‖fs μ l (wd7 X l Φ i) (wd7 X l Φ i) c t‖ ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ F : Cf r l.succ → ℝ, Integrable F ∧
      ∀ t ∈ Metric.ball t0 ε, ∀ c' : Cf r l.succ,
        ‖wtI l.succ c' * pairAt μ Φ Φ (glue l.succ (Function.update c l t) c')‖ ≤ F c' := by
  have : SFinite μ := sfinite_of_isHaarOn _ μ hμ
  choose ε hε M hMb using hloc
  set ε0 := Finset.univ.inf' Finset.univ_nonempty ε with hε0def
  have hε0 : 0 < ε0 := (Finset.lt_inf'_iff _).2 fun i _ => hε i
  have hε0i : ∀ i, ε0 ≤ ε i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have ht0n : 0 < ‖t0‖ := norm_pos_iff.2 ht0
  set δ : ℝ := min (‖t0‖ / 4) (ε0 / 4) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ ‖t0‖ / 4 := min_le_left _ _
  have hδ2 : δ ≤ ε0 / 4 := min_le_right _ _
  set B' := Metric.closedBall t0 (2 * δ) with hB'
  have hB : ∀ s ∈ B', s ≠ 0 := by
    intro s hs h0
    rw [h0, Metric.mem_closedBall, dist_zero_left] at hs
    linarith
  have hBε : ∀ s ∈ B', ∀ i, s ∈ Metric.ball t0 (ε i) := by
    intro s hs i
    rw [Metric.mem_closedBall] at hs
    rw [Metric.mem_ball]
    linarith [hε0i i]
  obtain ⟨K, hK0, hK⟩ := pt_sob (k := k) (r := r) (z := z) (z' := z') (π := π) (π' := π') hS t0 δ hδ hB
  have hwlc := seven_derivatives_preserve_compact X l hΦ

  set P : Fin 7 → ℂ × Cf r l.succ → ℂ := fun i q =>
    pairAt μ (wd7 X l Φ i) (wd7 X l Φ i) (glue l.succ (Function.update c l q.1) q.2) with hPdef
  have hPm : ∀ i, StronglyMeasurable (P i) := fun i =>
    (hM k r z z' Wp Wq π π' l c (wd7 X l Φ i) (wd7 X l Φ i)).stronglyMeasurable.integral_prod_right'
  have hPcont : ∀ i c', ContinuousOn (fun s => ‖P i (s, c')‖) B' := by
    intro i c' s hs
    simp only [hPdef, glue_succ_update_eq]
    by_cases hyO : Function.update (glue l.succ c c') l s ∈ OmX r
    · exact ((pairAt_hasFDerivAt X μ hμ l _ _ (hwlc i) (hwlc i) _ (hB s hs) hyO).continuousAt.norm).continuousWithinAt
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr (fun s' _ => ?_) ?_
      · rw [pairAt_off _ _ _ _ (omX_update_any _ l (hB s hs) hyO s'), norm_zero]
      · rw [pairAt_off _ _ _ _ hyO, norm_zero]
  have hPint : ∀ i c', IntegrableOn (fun s => ‖P i (s, c')‖) B' := fun i c' =>
    (hPcont i c').integrableOn_compact (isCompact_closedBall _ _)
  set F : Cf r l.succ → ℝ := fun c' => 4 * K * (‖wtI l.succ c'‖ * ∑ i, ∫ s in B', ‖P i (s, c')‖) with hF
  have hS0 : ∀ c', 0 ≤ ∑ i, ∫ s in B', ‖P i (s, c')‖ := fun c' =>
    Finset.sum_nonneg fun i _ => setIntegral_nonneg measurableSet_closedBall fun s _ => norm_nonneg _
  have hF0 : ∀ c', 0 ≤ F c' := fun c' => by
    have := hS0 c'
    simp only [hF]
    positivity
  refine ⟨δ, hδ, F, ?_, ?_⟩
  ·
    have hFm : Measurable F := by
      simp only [hF]
      refine measurable_const.mul ((wtI_measurable l.succ).norm.mul (Finset.measurable_sum _ fun i _ => ?_))
      exact ((hPm i).norm.integral_prod_left (μ := volume.restrict B')).measurable
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hF0)]
    have hper : ∀ c', ENNReal.ofReal (F c') = ENNReal.ofReal (4 * K) *
        ∑ i, ∫⁻ s in B', ENNReal.ofReal ‖wtI l.succ c' * P i (s, c')‖ := by
      intro c'
      simp only [hF]
      rw [ENNReal.ofReal_mul (by positivity), Finset.mul_sum,
        ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (norm_nonneg _)
          (setIntegral_nonneg measurableSet_closedBall fun s _ => norm_nonneg _)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal ((hPint i c').const_mul _)
        (Eventually.of_forall fun _ => by positivity)]
      simp only [norm_mul]
    have hswap : ∀ i, ∫⁻ c', ∫⁻ s in B', ENNReal.ofReal ‖wtI l.succ c' * P i (s, c')‖ =
        ∫⁻ s in B', ∫⁻ c', ENNReal.ofReal ‖wtI l.succ c' * P i (s, c')‖ := by
      intro i
      refine lintegral_lintegral_swap ?_
      have hm : Measurable (fun q : Cf r l.succ × ℂ => ENNReal.ofReal ‖wtI l.succ q.1 * P i (q.2, q.1)‖) :=
        ENNReal.measurable_ofReal.comp
          (((wtI_measurable l.succ).comp measurable_fst).mul ((hPm i).measurable.comp measurable_swap)).norm
      exact hm.aemeasurable
    have hinner : ∀ i, ∀ s ∈ B', ∫⁻ c', ENNReal.ofReal ‖wtI l.succ c' * P i (s, c')‖ ≤ ENNReal.ofReal (M i) := by
      intro i s hs
      have hL := (hMb i s (hBε s hs i)).1
      rw [← ofReal_integral_eq_lintegral_ofReal hL.norm (Eventually.of_forall fun _ => norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← norm_fs_self]
      exact (hMb i s (hBε s hs i)).2
    calc ∫⁻ c', ENNReal.ofReal (F c') = ENNReal.ofReal (4 * K) *
          ∑ i, ∫⁻ s in B', ∫⁻ c', ENNReal.ofReal ‖wtI l.succ c' * P i (s, c')‖ := by
          simp_rw [hper]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          rw [lintegral_finsetSum']
          · exact Finset.sum_congr rfl fun i _ => hswap i
          · intro i _
            exact ((ENNReal.measurable_ofReal.comp (((wtI_measurable l.succ).comp measurable_fst).mul
              ((hPm i).measurable.comp measurable_swap)).norm).lintegral_prod_right'
                (ν := volume.restrict B')).aemeasurable
      _ ≤ ENNReal.ofReal (4 * K) * ∑ i, ∫⁻ s in B', ENNReal.ofReal (M i) := by
          exact mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ =>
            setLIntegral_mono' measurableSet_closedBall fun s hs => hinner i s hs)
      _ < ⊤ := by
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun i _ => ?_)
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  ·
    intro t ht c'
    rw [glue_succ_update_eq, norm_mul]
    set y := glue l.succ c c' with hy
    by_cases hyO : Function.update y l t ∈ OmX r
    swap
    · rw [pairAt_off _ _ _ _ hyO, norm_zero, mul_zero]; exact hF0 c'
    have hP : ‖pairAt μ Φ Φ (Function.update y l t)‖ ≤ 4 * K * ∑ i, ∫ s in B', ‖P i (s, c')‖ := by
      have hx_int : ∀ Ξ ∈ lcSub k r z z' π π', ∀ s, Integrable (fun x : Mt k r =>
          ‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of x))‖ ^ 2) μ := by
        intro Ξ hΞ s
        have := (int_lc μ hμ hΞ hΞ (Function.update y l s)).norm
        simpa only [norm_hsInner_self] using this
      have hpair : ∀ Ξ : RadSp k r z z' π π', ∀ s, ‖pairAt μ Ξ Ξ (Function.update y l s)‖ =
          ∫ x, ‖hsVecR ((Ξ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of x))‖ ^ 2 ∂μ := by
        intro Ξ s; rw [norm_pairAt_selfI]; simp only [norm_hsInner_self]
      have hPy : ∀ i s, ‖P i (s, c')‖ = ‖pairAt μ (wd7 X l Φ i) (wd7 X l Φ i) (Function.update y l s)‖ := by
        intro i s; simp only [hPdef, glue_succ_update_eq, hy]
      have hsint : ∀ x : Mt k r, IntegrableOn (fun s => 4 * ∑ i, ‖hsVecR ((wd7 X l Φ i : Fn k r (Wq →L[ℂ] Wp))
          (Function.update y l s) (Matrix.of x))‖ ^ 2) B' := fun x =>
        (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => fun s hs =>
          ((sl_hasFDerivAt X l (wd7 X l Φ i) y (Matrix.of x) (hB s hs)).continuousAt.norm.pow 2).continuousWithinAt)
          ).integrableOn_compact (isCompact_closedBall _ _)
      have hmeas : Measurable (fun q : Mt k r × ℂ => ENNReal.ofReal (4 * ∑ i, ‖hsVecR ((wd7 X l Φ i :
          Fn k r (Wq →L[ℂ] Wp)) (Function.update y l q.2) (Matrix.of q.1))‖ ^ 2)) := by
        refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_))
        have hm := hM k r z z' Wp Wq π π' l c (wd7 X l Φ i) (wd7 X l Φ i)
        have hc : Measurable (fun q : Mt k r × ℂ => (((q.2, c') : ℂ × Cf r l.succ), q.1)) := by fun_prop
        have e : (fun q : Mt k r × ℂ => ‖hsVecR ((wd7 X l Φ i : Fn k r (Wq →L[ℂ] Wp))
            (Function.update y l q.2) (Matrix.of q.1))‖ ^ 2) = fun q => ‖B.hsInner
              ((wd7 X l Φ i : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.2) c') (Matrix.of q.1))
              ((wd7 X l Φ i : Fn k r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l q.2) c') (Matrix.of q.1))‖ := by
          funext q; rw [glue_succ_update_eq, norm_hsInner_self]
        rw [e]
        exact (hm.comp hc).norm
      have hinner : ∀ s, ∫⁻ x, ENNReal.ofReal (4 * ∑ i, ‖hsVecR ((wd7 X l Φ i : Fn k r (Wq →L[ℂ] Wp))
          (Function.update y l s) (Matrix.of x))‖ ^ 2) ∂μ = ENNReal.ofReal (4 * ∑ i, ‖P i (s, c')‖) := by
        intro s
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrable_finsetSum _ fun i _ => hx_int _ (hwlc i) s).const_mul 4)
          (Eventually.of_forall fun _ => by positivity)]
        congr 1
        rw [integral_const_mul, integral_finsetSum _ fun i _ => hx_int _ (hwlc i) s]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [hPy, hpair]
      have hRHS0 : 0 ≤ 4 * K * ∑ i, ∫ s in B', ‖P i (s, c')‖ := by
        have := hS0 c'
        positivity
      rw [← ENNReal.ofReal_le_ofReal_iff hRHS0, hpair Φ t,
        ofReal_integral_eq_lintegral_ofReal (hx_int Φ hΦ t) (Eventually.of_forall fun _ => by positivity)]
      calc ∫⁻ x, ENNReal.ofReal (‖hsVecR ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of x))‖ ^ 2) ∂μ
          ≤ ∫⁻ x, (ENNReal.ofReal K * ∫⁻ s in B', ENNReal.ofReal (4 * ∑ i, ‖hsVecR ((wd7 X l Φ i :
              Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of x))‖ ^ 2)) ∂μ := by
            refine lintegral_mono fun x => ?_
            rw [← ofReal_integral_eq_lintegral_ofReal (hsint x) (Eventually.of_forall fun _ => by positivity),
              ← ENNReal.ofReal_mul hK0]
            exact ENNReal.ofReal_le_ofReal (hK X l Φ y (Matrix.of x) t ht)
        _ = ENNReal.ofReal K * ∫⁻ s in B', ∫⁻ x, ENNReal.ofReal (4 * ∑ i, ‖hsVecR ((wd7 X l Φ i :
              Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of x))‖ ^ 2) ∂μ := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            exact lintegral_lintegral_swap hmeas.aemeasurable
        _ = ENNReal.ofReal K * ∫⁻ s in B', ENNReal.ofReal (4 * ∑ i, ‖P i (s, c')‖) := by
            simp_rw [hinner]
        _ = ENNReal.ofReal (4 * K * ∑ i, ∫ s in B', ‖P i (s, c')‖) := by
            rw [← ofReal_integral_eq_lintegral_ofReal
              ((integrable_finsetSum _ fun i _ => hPint i c').const_mul 4)
              (Eventually.of_forall fun _ => mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => norm_nonneg _)),
              ← ENNReal.ofReal_mul hK0]
            congr 1
            rw [integral_const_mul, integral_finsetSum _ fun i _ => hPint i c']
            ring
    calc ‖wtI l.succ c'‖ * ‖pairAt μ Φ Φ (Function.update y l t)‖
        ≤ ‖wtI l.succ c'‖ * (4 * K * ∑ i, ∫ s in B', ‖P i (s, c')‖) :=
          mul_le_mul_of_nonneg_left hP (norm_nonneg _)
      _ = F c' := by simp only [hF]; ring

end Main

section Gen

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def wlist7 : Fin 7 → List (Fin 6) :=
  ![[], [2, 0], [5, 3], [2, 0, 2, 0], [5, 3, 2, 0], [2, 0, 5, 3], [5, 3, 5, 3]]

theorem seven_derivatives_of_word_operator (X : ActualOps k r z z' π π') (l : Fin r) (js : List (Fin 6)) (Ψ : RadSp k r z z' π π')
    (i : Fin 7) : wd7 X l (wOp X l js Ψ) i = wOp X l (wlist7 i ++ js) Ψ := by
  fin_cases i <;>
    simp [wd7, wlist7, wOp, dT, dTb, List.map_cons, List.prod_cons, Module.End.mul_apply, mul_assoc]

theorem wOp_lcJ (X : ActualOps k r z z' π π') (l : Fin r) (js : List (Fin 6)) :
    ∀ Ψ ∈ lcSub k r z z' π π', wOp X l js Ψ ∈ lcSub k r z z' π π' := by
  induction js with
  | nil => intro Ψ h; simpa [wOp] using h
  | cons j js ih =>
    intro Ψ h
    have e : wOp X l (j :: js) Ψ = X.op l j (wOp X l js Ψ) := by
      simp [wOp, List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [e]
    exact op_lc X l j _ (ih Ψ h)

end Gen

theorem jSliceGenC_of_sob2_meas_locality (hS : JSSob2) (hM : JSMeas) (hL : SpectralL2Locality) : JSliceGenC := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl c hc Ψ hΨ
  refine ⟨hΨ.1, fun js t0 ht0 => ?_⟩
  refine slDom_of_loc hS hM X μ hD.2.1 l c (wOp X l js Ψ) (wOp_lcJ X l js Ψ hΨ.1) t0 ht0 fun i => ?_
  rw [seven_derivatives_of_word_operator]
  exact hL Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl c hc Ψ hΨ (wlist7 i ++ js) t0 ht0

end Formalism.FourierDecayAlt.P.CutSE
