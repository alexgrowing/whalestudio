import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_PtwCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.L2BoundAtBuiltPlaceHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOpenDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section general

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jgq_continuousOn (D : B.RealPlaceData k r Wp Wq) {A : ℝ} {H : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hT : JF.TransportedAlt k r A 0) (hH : B.InCC A 0 H) :
    ContinuousOn (fun q => B.JF D H (B.gq D q)) (JF.QDom k r D.z D.z') := by
  exact (Formalism.FourierDecayAlt.Final.jf_jqSmooth k r Wp Wq D A 0 H hT hH).continuousOn

theorem aesm_weight_smul (D : B.RealPlaceData k r Wp Wq) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (Fin r → ℂ) × ℂ → E} (hc : ContinuousOn g (JF.QDom k r D.z D.z')) :
    AEStronglyMeasurable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q • g q) volume := by
  set s := JF.QDom k r D.z D.z' with hs_def
  have hs : MeasurableSet s := by
    have hseq : s = (⋂ a : Fin r, {q : (Fin r → ℂ) × ℂ | q.1 a ≠ 0}) ∩
        {q | Tz k r D.z * Tz k r D.z' < Complex.normSq q.2} := by
      ext q
      simp [hs_def, JF.QDom]
    rw [hseq]
    refine IsOpen.measurableSet (IsOpen.inter (isOpen_iInter_of_finite fun a => ?_) ?_)
    · exact isOpen_ne_fun ((continuous_apply a).comp continuous_fst) continuous_const
    · exact isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd)
  have contW : Continuous (fun q : (Fin r → ℂ) × ℂ => (∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Mdim k r a - 2))) *
      (Complex.normSq q.2 - Tz k r D.z * Tz k r D.z') ^ (k - 1)) := by
    first | fun_prop | continuity
  have hw : ContinuousOn (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q) s := by
    refine contW.continuousOn.congr fun q hq => ?_
    unfold bcWeight
    rw [if_pos hq.2.le]
  have h1 : AEStronglyMeasurable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q • g q)
      (volume.restrict s) := (hw.smul hc).aestronglyMeasurable hs
  have h2 := (aestronglyMeasurable_indicator_iff hs).mpr h1
  refine h2.congr ?_
  have hN1 : ∀ a : Fin r, volume {q : (Fin r → ℂ) × ℂ | q.1 a = 0} = 0 := by
    intro a
    have h0 : volume {x : Fin r → ℂ | x a = 0} = 0 := by
      have he : {x : Fin r → ℂ | x a = 0} = Function.eval a ⁻¹' {0} := rfl
      rw [he, MeasureTheory.volume_pi]
      first
        | exact MeasureTheory.Measure.pi_eval_preimage_null _ (measure_singleton 0)
        | exact MeasureTheory.Measure.pi_eval_preimage_null (measure_singleton 0)
    exact MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null
      MeasureTheory.Measure.quasiMeasurePreserving_fst h0
  have hN2 : volume {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = Tz k r D.z * Tz k r D.z'} = 0 := by
    have hsph : volume (Metric.sphere (0 : ℂ) (Real.sqrt (Tz k r D.z * Tz k r D.z'))) = 0 := by
      first
        | exact MeasureTheory.Measure.addHaar_sphere volume (0 : ℂ) _
        | exact MeasureTheory.Measure.addHaar_sphere (0 : ℂ) _
    have h0 : volume {z : ℂ | Complex.normSq z = Tz k r D.z * Tz k r D.z'} = 0 := by
      refine measure_mono_null (fun z hz => ?_) hsph
      simp only [Set.mem_setOf_eq] at hz
      rw [mem_sphere_zero_iff_norm, ← hz, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    exact MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null
      MeasureTheory.Measure.quasiMeasurePreserving_snd h0
  have hA : ∀ᵐ q ∂(volume : Measure ((Fin r → ℂ) × ℂ)), ∀ a : Fin r, q.1 a ≠ 0 :=
    ae_all_iff.mpr fun a => ae_iff.mpr (by simpa using hN1 a)
  have hB : ∀ᵐ q ∂(volume : Measure ((Fin r → ℂ) × ℂ)), Complex.normSq q.2 ≠ Tz k r D.z * Tz k r D.z' :=
    ae_iff.mpr (by simpa using hN2)
  filter_upwards [hA, hB] with q hqa hqb
  classical
  by_cases hq : q ∈ s
  · simp [Set.indicator_apply, hq]
  · simp only [Set.indicator_apply, hq, if_false]
    have hlt : Complex.normSq q.2 < Tz k r D.z * Tz k r D.z' := by
      have hn : ¬ (Tz k r D.z * Tz k r D.z' < Complex.normSq q.2) := fun h => hq ⟨hqa, h⟩
      exact lt_of_le_of_ne (not_lt.mp hn) hqb
    have hz : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 := by
      unfold bcWeight
      rw [if_neg (not_le.mpr hlt)]
    rw [hz, zero_smul]

end general

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rr0Int_integrable (p : KB.Pl P Wp Wq) (w : List C.Letter) {A : ℝ} {H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hAB : B.AB P.k P.r ≤ A) (hT : JF.TransportedAlt P.k P.r A 0)
    (hH : ∀ j : ℕ, j ≤ 5 + (2 * P.r + P.k + 1) * w.length → B.InCC A j H) :
    Integrable (levelZeroRadialIntegral p w H) := by
  set D := p.T.base with hD
  set K := Formalism.FourierDecayAlt.P.CutMP.En.foldCV P.k P.r (M.sgn P p.l0) w H with hK
  have hKj : ∀ j ≤ 5, B.InCC A j K := fun j hj =>
    Formalism.FourierDecayAlt.P.CutMP.En.inCC_fold Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class A (M.sgn P p.l0) H w j (hH _ (by omega))
  have hHj : ∀ j ≤ 5, B.InCC A j H := fun j hj => hH j (by omega)
  obtain ⟨_, _, _, hB1, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi P.k P.r Wp Wq D A hAB
  obtain ⟨C0, hC0⟩ := hB1
  obtain ⟨cH, hcH⟩ := hHj 4 (by norm_num)
  obtain ⟨cK, hcK⟩ := hKj 4 (by norm_num)
  have hNH := (hC0 H H cH cH (hHj 5 le_rfl) (hHj 5 le_rfl) hcH hcH).1
  have hNK := (hC0 K K cK cK (hKj 5 le_rfl) (hKj 5 le_rfl) hcK hcK).1
  have cH' := jgq_continuousOn D hT (hHj 0 (by norm_num))
  have cK' := jgq_continuousOn D hT (hKj 0 (by norm_num))
  set W := bcWeight P.k P.r (Tz P.k P.r D.z) (Tz P.k P.r D.z') with hW
  have hW0 : ∀ q, 0 ≤ W q := fun q => Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q
  have hcv := Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff (V := Wp) (W := Wq)
  have ca : ContinuousOn (fun q => B.hsVec (B.JF D H (B.gq D q))) (JF.QDom P.k P.r D.z D.z') :=
    hcv.continuous.comp_continuousOn cH'
  have cb : ContinuousOn (fun q => B.hsVec (B.JF D K (B.gq D q))) (JF.QDom P.k P.r D.z D.z') :=
    hcv.continuous.comp_continuousOn cK'
  have hform : levelZeroRadialIntegral p w H = fun q => W q • inner ℂ (B.hsVec (B.JF D H (B.gq D q)))
      (B.hsVec (B.JF D K (B.gq D q))) := by
    funext q
    rw [Complex.real_smul]
    rfl
  have hm : AEStronglyMeasurable (levelZeroRadialIntegral p w H) volume := by
    rw [hform]; exact aesm_weight_smul D (ca.inner cb)
  refine ⟨hm, ?_⟩

  have ma : AEMeasurable (fun q => ENNReal.ofReal (W q * ‖B.hsVec (B.JF D H (B.gq D q))‖ ^ 2)) volume := by
    have := (aesm_weight_smul D ((ca.norm.pow 2))).aemeasurable
    exact ENNReal.measurable_ofReal.comp_aemeasurable (this.congr (ae_of_all _ fun q => rfl))
  have hle : ∀ q, ‖levelZeroRadialIntegral p w H q‖ₑ ≤ ENNReal.ofReal (W q * ‖B.hsVec (B.JF D H (B.gq D q))‖ ^ 2) +
      ENNReal.ofReal (W q * ‖B.hsVec (B.JF D K (B.gq D q))‖ ^ 2) := by
    intro q
    rw [hform, ← ofReal_norm, ← ENNReal.ofReal_add (mul_nonneg (hW0 q) (sq_nonneg _))
      (mul_nonneg (hW0 q) (sq_nonneg _))]
    refine ENNReal.ofReal_le_ofReal ?_
    set a := ‖B.hsVec (B.JF D H (B.gq D q))‖
    set b := ‖B.hsVec (B.JF D K (B.gq D q))‖
    have hi : ‖inner ℂ (B.hsVec (B.JF D H (B.gq D q))) (B.hsVec (B.JF D K (B.gq D q)))‖ ≤ a * b :=
      norm_inner_le_norm _ _
    rw [norm_smul, Real.norm_of_nonneg (hW0 q)]
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have h2 : a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
    nlinarith [hW0 q, mul_le_mul_of_nonneg_left (hi.trans h2) (hW0 q)]
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_add_left' ma]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · exact lt_top_iff_ne_top.2 hNH
  · exact lt_top_iff_ne_top.2 hNK

end place

end

end Formalism.FourierDecayAlt.P.CutBP
