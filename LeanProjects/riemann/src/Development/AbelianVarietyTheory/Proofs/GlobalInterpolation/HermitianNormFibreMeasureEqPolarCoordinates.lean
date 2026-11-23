import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralComplexEqLintegralSqrtMulExp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint

noncomputable section

namespace GlobalTheory.FibrePolar

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
  GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem restrict_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℝ)
    (O U U' : Set V) (fib fib' : ℝ → Measure V) (β : ℝ)
    (hf : Measurable f) (hO : IsOpen O) (hU : O ⊆ U) (hU' : O ⊆ U')
    (h : IsFibreFamily μ f id U (volume : Measure ℝ) Set.univ fib)
    (h' : IsFibreFamily μ f id U' (volume : Measure ℝ) Set.univ fib') :
    (fib β).restrict O = (fib' β).restrict O := by
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  have hc0 : ∀ n : Measure V, n.restrict O Oᶜ = 0 := fun n => by
    rw [Measure.restrict_apply hO.measurableSet.compl]; simp
  refine measure_eq_of_lintegral_eq_on_compactSupport _ _ O hO (hc0 _) (hc0 _) ?_
  intro φ hφ hc hs h0
  obtain ⟨hi, hg⟩ := h.2.2 φ hφ hc (hs.trans hU)
  obtain ⟨hi', hg'⟩ := h'.2.2 φ hφ hc (hs.trans hU')
  refine ⟨(hi β trivial).restrict, ?_⟩
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hφ0 : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]
  have hr : ∀ n : Measure V, ∫⁻ v in O, ENNReal.ofReal (φ v) ∂n =
      ∫⁻ v, ENNReal.ofReal (φ v) ∂n := fun n =>
    setLIntegral_eq_of_support_subset fun v hv => by
      by_contra hvO; exact hv (hφ0 v hvO)
  rw [hr, hr]
  have c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) Set.univ :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi b hb) (Filter.Eventually.of_forall h0)).symm
  have c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) Set.univ :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg').congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm
  have hae : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =ᵐ[volume.restrict Set.univ]
      (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (c.aemeasurable MeasurableSet.univ)
      (c'.aemeasurable MeasurableSet.univ) fun S hS _ => ?_
    rw [Measure.restrict_univ,
      ← IsFibreFamily_lintegral_preimage hf hO hU h _ hφm hφ0 _ hS,
      ← IsFibreFamily_lintegral_preimage hf hO hU' h' _ hφm hφ0 _ hS]
  exact Measure.eqOn_open_of_ae_eq hae isOpen_univ c c' trivial

variable {P Q P' Q' : ℕ}

theorem continuous_qf : Continuous (qf : Sp P Q → ℝ) := by
  unfold qf
  fun_prop

def glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q') : Sp P Q :=
  fun i => (e.symm i).elim p.1 p.2

@[simp] theorem glue_none (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q') :
    glue e p (e none) = p.1 := by simp [glue]

@[simp] theorem glue_some (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q')
    (i : Fin P' ⊕ Fin Q') : glue e p (e (some i)) = p.2 i := by simp [glue]

theorem continuous_glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (glue e) := by
  refine continuous_pi fun i => ?_
  obtain ⟨j, rfl⟩ := e.surjective i
  rcases j with _ | j
  · simp only [glue_none]; fun_prop
  · simp only [glue_some]; fun_prop

theorem measurePreserving_glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    MeasurePreserving (glue e) ((volume : Measure ℂ).prod volume) volume := by
  refine ⟨(continuous_glue e).measurable, ?_⟩
  rw [volume_pi (α := fun _ : Fin P ⊕ Fin Q => ℂ)]
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (continuous_glue e).measurable (MeasurableSet.univ_pi hs)]
  have : glue e ⁻¹' Set.pi Set.univ s =
      s (e none) ×ˢ Set.pi Set.univ (fun i => s (e (some i))) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_prod]
    rw [e.surjective.forall, Option.forall]
    simp
  rw [this, Measure.prod_prod, volume_pi_pi, ← e.prod_comp, Fintype.prod_option]

theorem norm_le_glue (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℂ × Sp P' Q') :
    ‖p.2‖ ≤ ‖glue e p‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simpa using norm_le_pi_norm (glue e p) (e (some i))

theorem qf_glue {e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)} (he : SignCompat e)
    (p : ℂ × Sp P' Q') : qf (glue e p) = sg (e none) * Complex.normSq p.1 + qf p.2 := by
  rw [qf_eq_sum, qf_eq_sum, ← e.sum_comp, Fintype.sum_option]
  simp only [glue_none, glue_some, he _]

def pt (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (a : ℝ × (ℝ × Sp P' Q')) : Sp P Q :=
  glue e ((Real.sqrt (sg (e none) * (a.1 - qf a.2.2)) : ℂ) *
    Complex.exp ((a.2.1 : ℂ) * Complex.I), a.2.2)

theorem continuous_pt (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) : Continuous (pt e) := by
  have := @continuous_qf P' Q'
  exact (continuous_glue e).comp (by fun_prop)

theorem pt_sg (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (p : ℝ × Sp P' Q') :
    pt e (sg (e none), p) = polarPt e p := by
  have : sg (e none) * (sg (e none) - qf p.2) = 1 - sg (e none) * qf p.2 := by
    rcases sg_eq (e none) with h | h <;> rw [h] <;> ring
  simp only [pt, this]
  rfl

def base (P' Q' : ℕ) : Measure (ℝ × Sp P' Q') :=
  ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)).prod volume

def fam (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ) : Measure (Sp P Q) :=
  ((2 : ℝ≥0∞) ^ (P' + Q')) •
    ((base P' Q').map fun p => pt e (t, p)).restrict {y | y (e none) ≠ 0}

theorem isFibreFamily_fam {e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)} (he : SignCompat e) :
    IsFibreFamily (dx P Q) (qf : Sp P Q → ℝ) id {y | y (e none) ≠ 0} (volume : Measure ℝ)
      Set.univ (fam e) := by
  have hO : IsOpen {y : Sp P Q | y (e none) ≠ 0} :=
    isOpen_ne_fun (continuous_apply _) continuous_const
  set O := {y : Sp P Q | y (e none) ≠ 0} with hOdef
  have hk : ((2 : ℝ≥0∞) ^ (P' + Q')) ≠ ⊤ := by simp
  have hpt := continuous_pt e
  have hpt' : ∀ t, Continuous fun p => pt e (t, p) := fun t => hpt.comp (by fun_prop)
  have hε := sg_eq (e none)
  refine ⟨fun t => ?_, fun φ hφ => ?_, fun φ hφ hs ht => ?_⟩
  · have hS : MeasurableSet (qf ⁻¹' {id t} ∩ O)ᶜ :=
      ((continuous_qf.measurable (measurableSet_singleton t)).inter hO.measurableSet).compl
    rw [fam, Measure.smul_apply, Measure.restrict_apply hS,
      Measure.map_apply (hpt' t).measurable (hS.inter hO.measurableSet)]
    have : (fun p => pt e (t, p)) ⁻¹' ((qf ⁻¹' {id t} ∩ O)ᶜ ∩ O) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun p hp => hp.1 ⟨?_, hp.2⟩
      have h : 0 < sg (e none) * (t - qf p.2) := by
        by_contra h
        exact hp.2 (by simp [pt, Real.sqrt_eq_zero_of_nonpos (not_lt.1 h)])
      have hn : Complex.normSq ((Real.sqrt (sg (e none) * (t - qf p.2)) : ℂ) *
          Complex.exp ((p.1 : ℂ) * Complex.I)) = sg (e none) * (t - qf p.2) := by
        rw [map_mul, Complex.normSq_ofReal, Real.mul_self_sqrt h.le, Complex.normSq_eq_norm_sq,
          Complex.norm_exp_ofReal_mul_I]; simp
      change qf (glue e _) = t
      rw [qf_glue he, hn]
      rcases hε with h1 | h1 <;> rw [h1] <;> ring
    rw [this, measure_empty, smul_zero]
  · have hG : Measurable (O.indicator φ) := hφ.indicator hO.measurableSet
    have hJ := hG.comp hpt.measurable
    have e1 : ∀ t, ∫⁻ v, φ v ∂(fam e t) = (2 : ℝ≥0∞) ^ (P' + Q') *
        ∫⁻ y, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, O.indicator φ (pt e (t, θ, y)) := fun t => by
      rw [fam, lintegral_smul_measure, ← lintegral_indicator hO.measurableSet,
        lintegral_map hG (hpt' t).measurable, base,
        lintegral_prod_symm' (fun p => O.indicator φ (pt e (t, p)))
          (hG.comp (hpt' t).measurable), smul_eq_mul]
    simp only [e1]
    rw [lintegral_const_mul' _ _ hk, ← lintegral_indicator hO.measurableSet, dx,
      lintegral_smul_measure, smul_eq_mul, card_eq e, pow_succ, mul_assoc]
    congr 1
    rw [← (measurePreserving_glue e).lintegral_comp hG,
      lintegral_prod_symm' (fun a => O.indicator φ (glue e a))
        (hG.comp (continuous_glue e).measurable), ← lintegral_const_mul' _ _ (by simp)]
    symm
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun y => Eq.symm ?_
      rw [lintegral_complex_eq_lintegral_sqrt_mul_exp (sg (e none)) (qf y) hε
        (fun z => O.indicator φ (glue e (z, y)))
        (hG.comp ((continuous_glue e).measurable.comp measurable_prodMk_right))
        (Set.indicator_of_notMem (by simp [hOdef]) _), ← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_congr fun t => ?_
      rw [lintegral_const_mul' _ _ (by simp), ← mul_assoc,
        ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
      rfl
    · refine Measurable.aemeasurable ?_
      refine Measurable.lintegral_prod_right' (f := fun a : (ℝ × Sp P' Q') × ℝ =>
        O.indicator φ (pt e (a.1.1, a.2, a.1.2))) ?_
      exact hJ.comp (by fun_prop)
  · obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hs
    obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
    let b : ℝ × Sp P' Q' → ℝ := (Set.univ ×ˢ Metric.closedBall 0 R).indicator fun _ => C
    have hb : Integrable b (base P' Q') := by
      refine (integrable_indicator_iff
        (MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet)).2
        (integrableOn_const ?_ (by simp))
      rw [base, Measure.prod_prod]
      exact ENNReal.mul_ne_top (measure_ne_top _ _) measure_closedBall_lt_top.ne
    have hle : ∀ t p, ‖φ (pt e (t, p))‖ ≤ b p := fun t p => by
      by_cases h : p ∈ (Set.univ : Set ℝ) ×ˢ Metric.closedBall (0 : Sp P' Q') R
      · simp only [b, Set.indicator_of_mem h]; exact hC _
      · simp only [b, Set.indicator_of_notMem h]
        rw [image_eq_zero_of_notMem_tsupport (f := φ), norm_zero]
        intro h1
        exact h ⟨trivial, mem_closedBall_zero_iff.2 ((norm_le_glue e (_, p.2)).trans
          (mem_closedBall_zero_iff.1 (hR h1)))⟩
    have hm : ∀ t, AEStronglyMeasurable (fun p => φ (pt e (t, p))) (base P' Q') := fun t =>
      (hφ.comp (hpt' t)).aestronglyMeasurable
    constructor
    · intro t _
      refine Integrable.smul_measure (Integrable.restrict ?_) hk
      rw [integrable_map_measure hφ.aestronglyMeasurable (hpt' t).aemeasurable]
      exact hb.mono' (hm t) (ae_of_all _ (hle t))
    · have e2 : ∀ t, ∫ x, φ x ∂(fam e t) =
          ((2 : ℝ≥0∞) ^ (P' + Q')).toReal * ∫ p, φ (pt e (t, p)) ∂(base P' Q') := fun t => by
        rw [fam, integral_smul_measure, setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (ht h)),
          integral_map (hpt' t).aemeasurable hφ.aestronglyMeasurable, smul_eq_mul]
      simp only [e2]
      exact (continuous_const.mul (continuous_of_dominated hm (fun t => ae_of_all _ (hle t)) hb
        (ae_of_all _ fun p => hφ.comp (hpt.comp (by fun_prop))))).continuousOn

theorem fibre_eq_polar : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)),
    SignCompat e → ∀ fib : ℝ → Measure (Sp P Q), IsDxDq fib → ∀ S : Set (Sp P Q),
      MeasurableSet S → (∀ y ∈ S, y (e none) ≠ 0) →
      fib (sg (e none)) S = (2 : ℝ≥0∞) ^ (P' + Q') * (volume : Measure (ℝ × Sp P' Q'))
        {t | t.1 ∈ Set.Ioo (-Real.pi) Real.pi ∧ polarPt e t ∈ S} := by
  intro P Q P' Q' e he fib hfib S hS hS0
  have hO : IsOpen {y : Sp P Q | y (e none) ≠ 0} :=
    isOpen_ne_fun (continuous_apply _) continuous_const
  have key := restrict_eq (dx P Q) qf {y | y (e none) ≠ 0} {x | x ≠ 0} _ fib (fam e) (sg (e none))
    continuous_qf.measurable hO (fun y hy h0 => hy (congrFun h0 _)) subset_rfl hfib
    (isFibreFamily_fam he)
  have hsub : S ⊆ {y | y (e none) ≠ 0} := hS0
  have hm : Measurable fun p => pt e (sg (e none), p) :=
    ((continuous_pt e).comp (by fun_prop)).measurable
  rw [← Measure.restrict_eq_self _ hsub, key, Measure.restrict_eq_self _ hsub, fam,
    Measure.smul_apply, Measure.restrict_eq_self _ hsub, Measure.map_apply hm hS, smul_eq_mul,
    base, Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply (hm hS),
    ← Measure.volume_eq_prod]
  congr 2
  ext p
  simp [pt_sg, and_comm]

end GlobalTheory.FibrePolar
