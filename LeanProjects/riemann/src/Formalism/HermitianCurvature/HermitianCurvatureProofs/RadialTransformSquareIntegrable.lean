import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroFormIntegrableCompact

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section L2

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def wt0 (c' : Cf r 0) : ℂ := ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ)

theorem level_zero_weight_measurable : Measurable (wt0 (r := r)) := by
  unfold wt0
  have e : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg]; norm_cast
  simp_rw [e]
  exact Complex.measurable_ofReal.comp
    (Finset.measurable_prod _ fun l _ => ((measurable_norm.comp (measurable_pi_apply l)).pow_const 2).inv)

def LevelZeroSquareIntegrable (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun c' : Cf r 0 => wt0 c' * pairAt μ u u (glue 0 c c'))

theorem pairAt_meas0 (μ : Measure (Mt k r)) [SFinite μ] (u v : RadSp k r z z' π π') (c : Fin r → ℂ) :
    StronglyMeasurable (fun c' : Cf r 0 => pairAt μ u v (glue 0 c c')) :=
  (pair_measurable c u v).stronglyMeasurable.integral_prod_right'

theorem hsInner_self_ofReal (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  push_cast
  rfl

theorem norm_pairAt_self (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u u c‖ = ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ ∂μ := by
  unfold pairAt
  simp_rw [hsInner_self_ofReal]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun g => by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem norm_pairAt_le (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {u v : RadSp k r z z' π π'}
    (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u v c‖ ≤ ‖pairAt μ u u c‖ + ‖pairAt μ v v c‖ := by
  rw [norm_pairAt_self, norm_pairAt_self]
  unfold pairAt
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add (int_lc μ hμ hu hu c).norm (int_lc μ hμ hv hv c).norm]
  exact integral_mono (int_lc μ hμ hu hv c).norm ((int_lc μ hμ hu hu c).norm.add (int_lc μ hμ hv hv c).norm)
    fun g => norm_hs_le _ _

theorem int_cross (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : LevelZeroSquareIntegrable μ u c) (Iv : LevelZeroSquareIntegrable μ v c) :
    Integrable (fun c' : Cf r 0 => wt0 c' * pairAt μ u v (glue 0 c c')) := by
  refine (Iu.norm.add Iv.norm).mono'
    (level_zero_weight_measurable.aestronglyMeasurable.mul (pairAt_meas0 μ u v c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c' => ?_)
  show ‖wt0 c' * pairAt μ u v (glue 0 c c')‖ ≤
    ‖wt0 c' * pairAt μ u u (glue 0 c c')‖ + ‖wt0 c' * pairAt μ v v (glue 0 c c')‖
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_le μ hμ hu hv _) (norm_nonneg _)

theorem pairAt_zero_zero (μ : Measure (Mt k r)) (c : Fin r → ℂ) :
    pairAt μ (0 : RadSp k r z z' π π') 0 c = 0 := by
  unfold pairAt
  simp [hsInner_zero_left]

theorem pairAt_add_add (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {u v : RadSp k r z z' π π'}
    (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (u + v) (u + v) c = pairAt μ u u c + pairAt μ u v c + pairAt μ v u c + pairAt μ v v c := by
  unfold pairAt
  have e : ∀ g : Mt k r, B.hsInner (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) =
      B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) := by
    intro g
    show B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) + (v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) + (v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) = _
    rw [Formalism.FourierDecayAlt.P.B6.hsInner_add_left, Formalism.FourierDecayAlt.P.B6.hsInner_add_right, Formalism.FourierDecayAlt.P.B6.hsInner_add_right]
    ring
  have e2 : (∫ g : Mt k r, B.hsInner (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ∂μ) =
      ∫ g, ((fun g : Mt k r => B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)))) g ∂μ := by
    congr 1; funext g; rw [e g]; rfl
  rw [e2, integral_add' (((int_lc μ hμ hu hu c).add (int_lc μ hμ hu hv c)).add (int_lc μ hμ hv hu c))
      (int_lc μ hμ hv hv c),
    integral_add' ((int_lc μ hμ hu hu c).add (int_lc μ hμ hu hv c)) (int_lc μ hμ hv hu c),
    integral_add' (int_lc μ hμ hu hu c) (int_lc μ hμ hu hv c)]

variable (k r z z' π π') in

def squareIntegrableSmoothSubmoduleGL (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) :
    Submodule ℂ (RadSp k r z z' π π') where
  carrier := {u | u ∈ lcSub k r z z' π π' ∧ ∀ c, LevelZeroSquareIntegrable μ u c}
  zero_mem' := ⟨(lcSub k r z z' π π').zero_mem, fun c => by
    unfold LevelZeroSquareIntegrable
    simp only [pairAt_zero_zero, mul_zero]
    exact integrable_zero _ _ _⟩
  add_mem' := by
    rintro u v ⟨hu, Iu⟩ ⟨hv, Iv⟩
    refine ⟨(lcSub k r z z' π π').add_mem hu hv, fun c => ?_⟩
    unfold LevelZeroSquareIntegrable
    simp_rw [pairAt_add_add μ hμ hu hv, mul_add]
    exact (((Iu c).add (int_cross μ hμ hu hv c (Iu c) (Iv c))).add
      (int_cross μ hμ hv hu c (Iv c) (Iu c))).add (Iv c)
  smul_mem' := by
    rintro a u ⟨hu, Iu⟩
    refine ⟨(lcSub k r z z' π π').smul_mem a hu, fun c => ?_⟩
    unfold LevelZeroSquareIntegrable
    simp_rw [pairAt_smul_left, pairAt_smul_right]
    have e : (fun c' : Cf r 0 => wt0 c' * (a * ((starRingEnd ℂ) a * pairAt μ u u (glue 0 c c')))) =
        fun c' => (a * (starRingEnd ℂ) a) * (wt0 c' * pairAt μ u u (glue 0 c c')) := by
      funext c'; ring
    rw [e]
    exact (Iu c).const_mul _

theorem unimodular_multiplier_preserves_L2 (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ} (hW : multiplicationOperator W m)
    (hm : ∀ c g, ‖m c g‖ = 1) : ∀ u ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ, W u ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ := by
  rintro u ⟨hu, Iu⟩
  refine ⟨mul_lc hW u hu, fun c => ?_⟩
  have e : ∀ c0, pairAt μ (W u) (W u) c0 = pairAt μ u u c0 := by
    intro c0
    unfold pairAt
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show B.hsInner ((W u : Fn k r (Wq →L[ℂ] Wp)) c0 (Matrix.of g)) ((W u : Fn k r (Wq →L[ℂ] Wp)) c0 (Matrix.of g)) = _
    rw [hW u c0 (Matrix.of g), hsInner_smul_left', hsInner_smul_right', ← mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hm]
    simp
  unfold LevelZeroSquareIntegrable
  simp_rw [e]
  exact Iu c

theorem norm_fsv (s t : ℂ) : ‖fsv s t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have : (s * t - (starRingEnd ℂ) s * (starRingEnd ℂ) t).re = 0 := by
    rw [← map_mul, Complex.sub_re, Complex.conj_re, sub_self]
  rw [this, Real.exp_zero]

end L2

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem radial_transform_square_integrable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (F : Mx P.k P.r → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) :
    Φ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine ⟨jfCptLocAll Wp Wq P z z' π π' D F Φ hP hz hz' hπ hπ' hF hΦ, fun c => ?_⟩
  subst hz hz' hπ hπ'
  have h := level_zero_form_integrable_compact (S := Empty) D μ hμ (fun _ => F) (fun _ => F) (fun _ => Φ) (fun _ => Φ)
    (fun _ => hF.1.1) (fun _ => hF.1.1) (fun _ => hΦ) (fun _ => hΦ) c
  unfold LevelZeroSquareIntegrable
  simpa [wt0] using h

theorem compact_kernel_le_L2 (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') :
    herKc S P z z' π π' L st l0 D 0 ≤ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine Submodule.span_le.mpr fun Φ hΦ => ?_
  have key : ∀ (i : Fin (P.r + 1)) (Ψ : RadSp P.k P.r z z' π π'), HerGenC S P z z' π π' L st l0 D i Ψ →
      i = 0 → Ψ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
    intro i Ψ h
    induction h with
    | jf F Φ hF hΦ => exact fun _ => radial_transform_square_integrable P z z' π π' μ hμ D hP hz hz' hπ hπ' F hF Φ hΦ
    | slice l w a b Φ _ _ _ => exact fun h => absurd h (Fin.succ_ne_zero l)
    | waveC l w s Wv Wv' a b Φ _ h1 h2 _ ih =>
      intro h
      have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
          entSub (presAlg (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ)) :=
        (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (show mkP Wv Wv' ∈ presAlg _ from
          ⟨unimodular_multiplier_preserves_L2 μ hμ h1 (fun c _ => norm_fsv _ _), unimodular_multiplier_preserves_L2 μ hμ h2 (fun c _ => norm_fsv _ _)⟩)) (UUiw_mem s w)
      exact (hm a b).1 Φ (ih h)
    | waveZ w s Wv Wv' a b Φ _ h1 h2 _ ih =>
      intro h
      have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
          entSub (presAlg (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ)) :=
        (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (show mkP Wv Wv' ∈ presAlg _ from
          ⟨unimodular_multiplier_preserves_L2 μ hμ h1 (fun _ _ => norm_fsv _ _), unimodular_multiplier_preserves_L2 μ hμ h2 (fun _ _ => norm_fsv _ _)⟩)) (UUiw_mem s w)
      exact (hm a b).1 Φ (ih h)
  exact key 0 Φ hΦ rfl

end Classes

end Formalism.FourierDecayAlt.P5.HerC
