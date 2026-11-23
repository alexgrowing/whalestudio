import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralComplexEqLintegralSqrtMulExpStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPointStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadricStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversionHaarSymmFormStatement

noncomputable section

namespace GlobalTheory.RealPlaceCompare

open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal

variable {P Q P' Q' : ℕ}

theorem herm_eq (x y : PerpendicularEmbedding.Sp P Q) : ActionCoordinates.herm x y = PerpendicularEmbedding.herm x y := by
  simp [ActionCoordinates.herm, PerpendicularEmbedding.herm, ActionCoordinates.sgn, Fintype.sum_sum_type, sub_eq_add_neg]

theorem qf_eq : (ActionCoordinates.qf : PerpendicularEmbedding.Sp P Q → ℝ) = PerpendicularEmbedding.qf := by
  funext x
  rw [ActionCoordinates.qf, herm_eq, PerpendicularEmbedding.herm_self, Complex.ofReal_re]

theorem bil_eq (x y : PerpendicularEmbedding.Sp P Q) : ActionCoordinates.bil x y = 2 * (PerpendicularEmbedding.herm x y).re := by
  rw [ActionCoordinates.bil, herm_eq, Algebra.trace_complex_apply]

theorem dx_eq (P Q : ℕ) : ActionCoordinates.dx P Q = PerpendicularEmbedding.dx P Q := rfl

theorem cM_eq (M : ℕ) : ActionCoordinates.cM M = ENNReal.ofReal (PerpendicularEmbedding.cM M) := rfl

theorem act_eq (g : UpqT P Q) (x : PerpendicularEmbedding.Sp P Q) : ActionCoordinates.act g x = PerpendicularEmbedding.act g x := rfl

theorem isPerpFrame_iff (x₀ : PerpendicularEmbedding.Sp P Q) (A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ)
    (j : UpqT P' Q' → UpqT P Q) :
    ActionCoordinates.IsPerpFrame x₀ (Matrix.toLin' A) j ↔ PerpendicularEmbedding.IsPerpEmb x₀ A j := by
  simp only [ActionCoordinates.IsPerpFrame, PerpendicularEmbedding.IsPerpEmb, herm_eq, act_eq, Matrix.toLin'_apply]

theorem isPerpEmb_iff (x₀ : PerpendicularEmbedding.Sp P Q) (A : PerpendicularEmbedding.Sp P' Q' →ₗ[ℂ] PerpendicularEmbedding.Sp P Q)
    (j : UpqT P' Q' → UpqT P Q) :
    PerpendicularEmbedding.IsPerpEmb x₀ (LinearMap.toMatrix' A) j ↔ ActionCoordinates.IsPerpFrame x₀ A j := by
  rw [← isPerpFrame_iff, Matrix.toLin'_toMatrix']

theorem continuous_qf : Continuous (PerpendicularEmbedding.qf : PerpendicularEmbedding.Sp P Q → ℝ) := by
  unfold PerpendicularEmbedding.qf
  fun_prop

theorem qf_zero : PerpendicularEmbedding.qf (0 : PerpendicularEmbedding.Sp P Q) = 0 := by simp [PerpendicularEmbedding.qf]

def rho (j : Fin P ⊕ Fin Q) (x : PerpendicularEmbedding.Sp P Q) : ℝ :=
  Complex.normSq (x j) / ∑ i, Complex.normSq (x i)

theorem sum_normSq_ne {x : PerpendicularEmbedding.Sp P Q} (hx : x ≠ 0) : ∑ i, Complex.normSq (x i) ≠ 0 := by
  intro h
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _] at h
  exact hx (funext fun i => Complex.normSq_eq_zero.1 (h i (Finset.mem_univ i)))

theorem rho_nonneg (j : Fin P ⊕ Fin Q) (x : PerpendicularEmbedding.Sp P Q) : 0 ≤ rho j x :=
  div_nonneg (Complex.normSq_nonneg _) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

theorem sum_rho {x : PerpendicularEmbedding.Sp P Q} (hx : x ≠ 0) : ∑ j, rho j x = 1 := by
  unfold rho
  rw [← Finset.sum_div, div_self (sum_normSq_ne hx)]

theorem measurable_rho (j : Fin P ⊕ Fin Q) : Measurable (rho j) := by
  unfold rho
  refine Measurable.div (Continuous.measurable ?_) (Continuous.measurable ?_) <;> fun_prop

theorem continuousOn_rho (j : Fin P ⊕ Fin Q) : ContinuousOn (rho j) {x | x ≠ 0} := by
  unfold rho
  refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_)
    fun x hx => sum_normSq_ne hx <;> fun_prop

def glue (j : Fin P ⊕ Fin Q) (p : ℂ × ({i // i ≠ j} → ℂ)) : PerpendicularEmbedding.Sp P Q :=
  fun i => if h : i = j then p.1 else p.2 ⟨i, h⟩

theorem continuous_glue (j : Fin P ⊕ Fin Q) : Continuous (glue j) := by
  refine continuous_pi fun i => ?_
  unfold glue
  by_cases h : i = j <;> simp only [h, dite_true, dite_false] <;> fun_prop

theorem measurePreserving_glue (j : Fin P ⊕ Fin Q) :
    MeasurePreserving (glue j) ((volume : Measure ℂ).prod volume) volume := by
  have h1 := (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin P ⊕ Fin Q => ℂ)
    (fun i => i = j)).symm
  have h2 := ((volume_preserving_funUnique {i // i = j} ℂ).symm).prod
    (MeasurePreserving.id (volume : Measure ({i // i ≠ j} → ℂ)))
  have h3 := h1.comp (f := Prod.map (MeasurableEquiv.funUnique {i // i = j} ℂ).symm id)
    (μa := (volume : Measure ℂ).prod volume) (by rw [Measure.volume_eq_prod]; convert h2)
  have e : glue j = (MeasurableEquiv.piEquivPiSubtypeProd (fun _ => ℂ) fun i => i = j).symm ∘
      Prod.map (MeasurableEquiv.funUnique {i // i = j} ℂ).symm id := by
    funext p i
    by_cases h : i = j <;> simp [glue, h, MeasurableEquiv.piEquivPiSubtypeProd]
  rw [e]
  exact h3

theorem glue_self (j : Fin P ⊕ Fin Q) (p : ℂ × ({i // i ≠ j} → ℂ)) : glue j p j = p.1 := by
  simp [glue]

theorem norm_le_glue (j : Fin P ⊕ Fin Q) (p : ℂ × ({i // i ≠ j} → ℂ)) : ‖p.2‖ ≤ ‖glue j p‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have := norm_le_pi_norm (glue j p) i.1
  simpa [glue, i.2] using this

theorem qf_glue (j : Fin P ⊕ Fin Q) : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ z y,
    PerpendicularEmbedding.qf (glue j (z, y)) = ε * Complex.normSq z + PerpendicularEmbedding.qf (glue j (0, y)) := by
  have key : ∀ {n : ℕ} (k : Fin n) (u v : Fin n → ℂ), (∀ i, i ≠ k → u i = v i) → v k = 0 →
      ∑ i, Complex.normSq (u i) = Complex.normSq (u k) + ∑ i, Complex.normSq (v i) := by
    intro n k u v h h0
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
      ← Finset.add_sum_erase _ (fun i => Complex.normSq (v i)) (Finset.mem_univ k), h0, map_zero,
      zero_add]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.ne_of_mem_erase hi)]
  rcases j with k | k
  · refine ⟨1, Or.inl rfl, fun z y => ?_⟩
    unfold PerpendicularEmbedding.qf
    rw [key k (fun i => glue (Sum.inl k) (z, y) (Sum.inl i))
      (fun i => glue (Sum.inl k) (0, y) (Sum.inl i)) (fun i hi => by simp [glue, hi])
      (glue_self _ _), glue_self]
    simp [glue]; ring
  · refine ⟨-1, Or.inr rfl, fun z y => ?_⟩
    unfold PerpendicularEmbedding.qf
    rw [key k (fun i => glue (Sum.inr k) (z, y) (Sum.inr i))
      (fun i => glue (Sum.inr k) (0, y) (Sum.inr i)) (fun i hi => by simp [glue, hi])
      (glue_self _ _), glue_self]
    simp [glue]; ring

theorem exists_chart (j : Fin P ⊕ Fin Q) : ∃ fib : ℝ → Measure (PerpendicularEmbedding.Sp P Q),
    (∀ t, fib t (PerpendicularEmbedding.qf ⁻¹' {t} ∩ {x | x ≠ 0})ᶜ = 0) ∧
    (∀ φ : PerpendicularEmbedding.Sp P Q → ℝ≥0∞, Measurable φ → Measurable (fun t => ∫⁻ x, φ x ∂(fib t)) ∧
      ∫⁻ x, ENNReal.ofReal (rho j x) * φ x = ∫⁻ t, ∫⁻ x, φ x ∂(fib t)) ∧
    (∀ φ : PerpendicularEmbedding.Sp P Q → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {x | x ≠ 0} →
      (∀ t, Integrable φ (fib t)) ∧ Continuous (fun t => ∫ x, φ x ∂(fib t))) := by
  obtain ⟨ε, hε, hq⟩ := qf_glue j
  let c : ({i // i ≠ j} → ℂ) → ℝ := fun y => PerpendicularEmbedding.qf (glue j (0, y))
  have hc : Continuous c := continuous_qf.comp ((continuous_glue j).comp (by fun_prop))
  let ang : Measure ℝ := (2⁻¹ : ℝ≥0∞) • volume.restrict (Set.Ioo (-Real.pi) Real.pi)
  haveI : IsFiniteMeasure ang := ⟨by
    simp only [ang, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)⟩
  let m : Measure (({i // i ≠ j} → ℂ) × ℝ) := volume.prod ang
  let pt : ℝ × (({i // i ≠ j} → ℂ) × ℝ) → PerpendicularEmbedding.Sp P Q := fun a =>
    glue j ((Real.sqrt (ε * (a.1 - c a.2.1)) : ℂ) * Complex.exp ((a.2.2 : ℂ) * Complex.I), a.2.1)
  have hpt : Continuous pt := (continuous_glue j).comp (by fun_prop)
  have hpt' : ∀ t, Continuous fun p => pt (t, p) := fun t => hpt.comp (by fun_prop)
  have hd : Measurable fun x : PerpendicularEmbedding.Sp P Q => (rho j x).toNNReal :=
    (measurable_rho j).real_toNNReal
  have hd' : Measurable fun x : PerpendicularEmbedding.Sp P Q => ENNReal.ofReal (rho j x) :=
    (measurable_rho j).ennreal_ofReal
  have hl : ∀ (t : ℝ) (φ : PerpendicularEmbedding.Sp P Q → ℝ≥0∞), Measurable φ →
      ∫⁻ x, φ x ∂((m.map fun p => pt (t, p)).withDensity fun x => ENNReal.ofReal (rho j x)) =
        ∫⁻ p, ENNReal.ofReal (rho j (pt (t, p))) * φ (pt (t, p)) ∂m := fun t φ hφ => by
    rw [lintegral_withDensity_eq_lintegral_mul _ hd' hφ,
      lintegral_map (hd'.mul hφ) (hpt' t).measurable]
    rfl
  refine ⟨fun t => (m.map fun p => pt (t, p)).withDensity fun x => ENNReal.ofReal (rho j x),
    fun t => ?_, fun φ hφ => ?_, fun φ hφ hs ht => ?_⟩
  · have hS : MeasurableSet (PerpendicularEmbedding.qf ⁻¹' {t} ∩ {x : PerpendicularEmbedding.Sp P Q | x ≠ 0})ᶜ :=
      ((continuous_qf.measurable (measurableSet_singleton t)).inter isOpen_ne.measurableSet).compl
    rw [← lintegral_indicator_one hS, hl t _ (measurable_one.indicator hS)]
    refine (lintegral_congr fun p => ?_).trans lintegral_zero
    by_cases h : ε * (t - c p.1) ≤ 0
    · have : rho j (pt (t, p)) = 0 := by
        simp [rho, pt, glue_self, Real.sqrt_eq_zero_of_nonpos h]
      simp [this]
    · have h := lt_of_not_ge h
      have hn : Complex.normSq ((Real.sqrt (ε * (t - c p.1)) : ℂ) *
          Complex.exp ((p.2 : ℂ) * Complex.I)) = ε * (t - c p.1) := by
        rw [map_mul, Complex.normSq_ofReal, Real.mul_self_sqrt h.le, Complex.normSq_eq_norm_sq,
          Complex.norm_exp_ofReal_mul_I]; simp
      rw [Set.indicator_of_notMem, mul_zero]
      refine Set.notMem_compl_iff.2 ⟨?_, fun h0 => ?_⟩
      · change PerpendicularEmbedding.qf (glue j _) = t
        rw [hq, hn]
        rcases hε with rfl | rfl <;> simp [c]
      · have h1 := congrFun h0 j
        simp only [pt, glue_self, Pi.zero_apply] at h1
        rw [h1, map_zero] at hn
        exact h.ne hn
  · simp only [hl _ φ hφ]
    have hG : Measurable fun x => ENNReal.ofReal (rho j x) * φ x := hd'.mul hφ
    have hJ := hG.comp hpt.measurable
    refine ⟨hJ.lintegral_prod_right', ?_⟩
    rw [← (measurePreserving_glue j).lintegral_comp hG,
      lintegral_prod_symm' (fun a => ENNReal.ofReal (rho j (glue j a)) * φ (glue j a))
        (hG.comp (continuous_glue j).measurable)]
    have e1 : ∀ t, ∫⁻ p, ENNReal.ofReal (rho j (pt (t, p))) * φ (pt (t, p)) ∂m =
        ∫⁻ y, ∫⁻ θ, ENNReal.ofReal (rho j (pt (t, y, θ))) * φ (pt (t, y, θ)) ∂ang := fun t =>
      lintegral_prod _ (hG.comp (hpt' t).measurable).aemeasurable
    simp only [e1]
    symm
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun y => Eq.symm ?_
      rw [GlobalTheory.T.lintegral_complex_eq_polar_sqrt ε (c y) hε
        (fun z => ENNReal.ofReal (rho j (glue j (z, y))) * φ (glue j (z, y)))
        (hG.comp ((continuous_glue j).measurable.comp measurable_prodMk_right))
        (by simp [rho, glue_self])]
      refine lintegral_congr fun t => ?_
      rw [lintegral_const_mul' _ _ (by simp), lintegral_smul_measure]
      rfl
    · refine Measurable.aemeasurable ?_
      refine Measurable.lintegral_prod_right' (f := fun a : (ℝ × ({i // i ≠ j} → ℂ)) × ℝ =>
        ENNReal.ofReal (rho j (pt (a.1.1, a.1.2, a.2))) * φ (pt (a.1.1, a.1.2, a.2))) ?_
      exact hJ.comp (by fun_prop)
  · let ψ : PerpendicularEmbedding.Sp P Q → ℝ := fun x => rho j x * φ x
    have hψ : Continuous ψ :=
      ((continuousOn_rho j).mul hφ.continuousOn).continuous_of_tsupport_subset isOpen_ne
        (tsupport_mul_subset_right.trans ht)
    have hψs : HasCompactSupport ψ := hs.mul_left
    have e : (fun x => (rho j x).toNNReal • φ x) = ψ := by
      funext x; simp [ψ, NNReal.smul_def, rho_nonneg]
    obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hψs
    obtain ⟨R, hR⟩ := hψs.isCompact.isBounded.subset_closedBall 0
    let b : ({i // i ≠ j} → ℂ) × ℝ → ℝ :=
      (Metric.closedBall 0 R ×ˢ Set.univ).indicator fun _ => C
    have hb : Integrable b m := by
      refine (integrable_indicator_iff
        (Metric.isClosed_closedBall.measurableSet.prod MeasurableSet.univ)).2
        (integrableOn_const ?_ (by simp))
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top measure_closedBall_lt_top.ne (measure_ne_top _ _)
    have hle : ∀ t p, ‖ψ (pt (t, p))‖ ≤ b p := fun t p => by
      by_cases h : p ∈ Metric.closedBall (0 : {i // i ≠ j} → ℂ) R ×ˢ (Set.univ : Set ℝ)
      · simp only [b, Set.indicator_of_mem h]; exact hC _
      · simp only [b, Set.indicator_of_notMem h]
        rw [image_eq_zero_of_notMem_tsupport (f := ψ), norm_zero]
        intro h1
        exact h ⟨mem_closedBall_zero_iff.2 ((norm_le_glue j (_, p.1)).trans
          (mem_closedBall_zero_iff.1 (hR h1))), trivial⟩
    have hm : ∀ t, AEStronglyMeasurable (fun p => ψ (pt (t, p))) m := fun t =>
      (hψ.comp (hpt' t)).aestronglyMeasurable
    constructor
    · intro t
      refine (integrable_withDensity_iff_integrable_smul hd).2 ?_
      rw [e, integrable_map_measure hψ.aestronglyMeasurable (hpt' t).aemeasurable]
      exact hb.mono' (hm t) (ae_of_all _ (hle t))
    · have e2 : ∀ t, ∫ x, φ x ∂((m.map fun p => pt (t, p)).withDensity
          fun x => ENNReal.ofReal (rho j x)) = ∫ p, ψ (pt (t, p)) ∂m := fun t => by
        refine (integral_withDensity_eq_integral_smul hd φ).trans ?_
        rw [e, integral_map (hpt' t).aemeasurable hψ.aestronglyMeasurable]
      simp only [e2]
      exact continuous_of_dominated hm (fun t => ae_of_all _ (hle t)) hb
        (ae_of_all _ fun p => hψ.comp (hpt.comp (by fun_prop)))

theorem exists_isDxDq (P Q : ℕ) : ∃ fib : ℝ → Measure (PerpendicularEmbedding.Sp P Q), PerpendicularEmbedding.IsDxDq fib := by
  choose F h1 h2 h3 using fun j : Fin P ⊕ Fin Q => exists_chart j
  have hk : ((2 : ℝ≥0∞) ^ (P + Q)) ≠ ⊤ := by simp
  refine ⟨fun t => ((2 : ℝ≥0∞) ^ (P + Q)) • ∑ j, F j t, fun t => ?_, fun φ hφ => ?_,
    fun φ hφ hs ht => ⟨fun t _ => ?_, ?_⟩⟩
  · rw [Measure.smul_apply, Measure.finset_sum_apply, id, Finset.sum_eq_zero fun j _ => h1 j t,
      smul_zero]
  · simp only [PerpendicularEmbedding.dx, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      lintegral_finset_sum_measure]
    rw [lintegral_const_mul' _ _ hk, lintegral_finset_sum _ fun j _ => (h2 j φ hφ).1,
      ← Finset.sum_congr rfl fun j _ => (h2 j φ hφ).2,
      ← lintegral_finset_sum _ (f := fun j x => ENNReal.ofReal (rho j x) * φ x)
        fun j _ => (measurable_rho j).ennreal_ofReal.mul hφ,
      ← lintegral_indicator isOpen_ne.measurableSet]
    congr 1
    refine lintegral_congr fun x => ?_
    by_cases hx : x = 0
    · simp [hx, rho]
    · rw [Set.indicator_of_mem (by exact hx), ← Finset.sum_mul,
        ← ENNReal.ofReal_sum_of_nonneg fun j _ => rho_nonneg j x, sum_rho hx]
      simp
  · exact (integrable_finset_sum_measure.2 fun j _ => (h3 j φ hφ hs ht).1 t).smul_measure hk
  · simp only [integral_smul_measure,
      integral_finset_sum_measure fun j _ => (h3 j φ hφ hs ht).1 _]
    exact (continuous_const.mul
      (continuous_finset_sum _ fun j _ => (h3 j φ hφ hs ht).2)).continuousOn

theorem isDxDq_local {fib : ℝ → Measure (PerpendicularEmbedding.Sp P Q)} (h : PerpendicularEmbedding.IsDxDq fib) (β : ℝ) :
    ActionCoordinates.IsDxDq β fib :=
  ⟨{x | x ≠ 0}, Set.univ, subset_rfl, isOpen_univ, trivial, by rw [qf_eq]; exact h⟩

theorem fib_eq {fib fib' : ℝ → Measure (PerpendicularEmbedding.Sp P Q)} {β : ℝ} (hβ : β ≠ 0)
    (h : PerpendicularEmbedding.IsDxDq fib) (h' : ActionCoordinates.IsDxDq β fib') : fib' β = fib β := by
  obtain ⟨U, B, hU, hB, hβB, h'⟩ := h'
  rw [qf_eq] at h'
  refine GlobalTheory.T.isFibreFamily_eq_at_continuity_point (PerpendicularEmbedding.dx P Q) PerpendicularEmbedding.qf {x | x ≠ 0} U {x | x ≠ 0} B Set.univ fib' fib β
    continuous_qf.measurable isOpen_ne hU subset_rfl ?_ hB isOpen_univ hβB trivial h' h
  rintro x hx rfl
  exact hβ (by simpa [qf_zero] using hx.symm)

theorem ae_qf {fib : ℝ → Measure (PerpendicularEmbedding.Sp P Q)} (h : PerpendicularEmbedding.IsDxDq fib) (β : ℝ) :
    ∀ᵐ y ∂(fib β), PerpendicularEmbedding.qf y = β := by
  have h1 : ∀ᵐ y ∂(fib β), y ∈ PerpendicularEmbedding.qf ⁻¹' {id β} ∩ {x | x ≠ 0} := h.1 β
  filter_upwards [h1] with y hy using hy.1

theorem sphere_iff : PerpendicularEmbedding.SphereMass ↔ ActionCoordinates.SphereVolume := by
  constructor
  · intro h M hM fib' hfib'
    obtain ⟨⟨fib, hfib⟩, h2⟩ := h M hM
    rw [fib_eq one_ne_zero hfib hfib', cM_eq, ← h2 fib hfib, qf_eq]
    exact measure_congr (Filter.eventuallyEq_univ.2 (ae_qf hfib 1))
  · intro h M hM
    refine ⟨exists_isDxDq M 0, fun fib hfib => ?_⟩
    rw [← cM_eq, ← h M hM fib (isDxDq_local hfib 1), qf_eq]
    exact (measure_congr (Filter.eventuallyEq_univ.2 (ae_qf hfib 1))).symm

theorem exists_test (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, HasCompactSupport Φ ∧ Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), h1, ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

theorem selfDual_iff_of_bilin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (e : ℝ) (β : V → V → ℝ)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ x y, e * β x y = B x y) (hs : ∀ x y, B x y = B y x)
    (hn : ∀ x, (∀ y, B x y = 0) → x = 0) (μ : Measure V) (hμ : μ.IsAddHaarMeasure) :
    SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((e * β x y : ℝ) : ℂ))) ↔
      ActionCoordinates.IsSelfDualFor e β μ := by
  obtain ⟨⟨c, -, hc⟩, hS⟩ := GlobalTheory.T.fourier_inversion_haar_symm_form_alt B hs hn μ hμ
  obtain ⟨Φ₀, h0, h1⟩ := exists_test V
  have key := hc Φ₀ Φ₀.continuous (hS Φ₀).1 (hS Φ₀).2 0
  unfold SelfDual ActionCoordinates.IsSelfDualFor ActionCoordinates.fourierT
  simp only [hB]
  constructor
  · rintro ⟨-, h⟩ Φ
    have := h Φ₀ Φ₀.continuous h0 (hS Φ₀).2 0
    rw [key, neg_zero, h1, mul_one] at this
    refine ⟨(hS Φ).1, (hS Φ).2, fun x => ?_⟩
    rw [hc Φ Φ.continuous (hS Φ).1 (hS Φ).2, this, one_mul]
  · intro h
    have := (h Φ₀).2.2 0
    rw [key, neg_zero, h1, mul_one] at this
    refine ⟨hμ, fun Φ hΦ hsup hI z => ?_⟩
    rw [hc Φ hΦ (hΦ.integrable_of_hasCompactSupport hsup) hI, this, one_mul]

theorem selfDual_iff_unique {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (e : ℝ) (β : V → V → ℝ)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ x y, e * β x y = B x y) (hs : ∀ x y, B x y = B y x)
    (hn : ∀ x, (∀ y, B x y = 0) → x = 0) (μ₀ : Measure V) (hμ₀ : μ₀.IsAddHaarMeasure) :
    SelfDual μ₀ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((e * β x y : ℝ) : ℂ))) ↔
      ∀ μ : Measure V, μ.IsAddHaarMeasure → (ActionCoordinates.IsSelfDualFor e β μ ↔ μ = μ₀) := by
  constructor
  · intro h μ hμ
    have h' := (selfDual_iff_of_bilin e β B hB hs hn μ₀ hμ₀).1 h
    refine ⟨fun h2 => ?_, fun h2 => h2 ▸ h'⟩
    obtain ⟨Φ₀, h0, h1⟩ := exists_test V
    exact SelfDual.eq_of_test h ((selfDual_iff_of_bilin e β B hB hs hn μ hμ).2 h2) Φ₀
      Φ₀.continuous h0 (h' Φ₀).2.1 0 (by rw [neg_zero, h1]; exact one_ne_zero)
  · intro h
    exact (selfDual_iff_of_bilin e β B hB hs hn μ₀ hμ₀).2 ((h μ₀ hμ₀).2 rfl)

theorem herm_add_left (x y z : PerpendicularEmbedding.Sp P Q) :
    PerpendicularEmbedding.herm (x + y) z = PerpendicularEmbedding.herm x z + PerpendicularEmbedding.herm y z := by
  simp only [PerpendicularEmbedding.herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring

theorem herm_smul_left (a : ℂ) (x z : PerpendicularEmbedding.Sp P Q) :
    PerpendicularEmbedding.herm (a • x) z = a * PerpendicularEmbedding.herm x z := by
  simp only [PerpendicularEmbedding.herm, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sub, Finset.mul_sum]

theorem herm_star (x z : PerpendicularEmbedding.Sp P Q) : star (PerpendicularEmbedding.herm x z) = PerpendicularEmbedding.herm z x := by
  simp [PerpendicularEmbedding.herm, mul_comm]

def realForm (e : ℝ) (P Q : ℕ) : PerpendicularEmbedding.Sp P Q →ₗ[ℝ] PerpendicularEmbedding.Sp P Q →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => e * (2 * (PerpendicularEmbedding.herm x y).re))
    (fun x y z => by rw [herm_add_left, Complex.add_re]; ring)
    (fun a x z => by
      rw [← Complex.coe_smul, herm_smul_left, Complex.re_ofReal_mul, smul_eq_mul]; ring)
    (fun x y z => by
      rw [← herm_star (y + z), ← herm_star y, ← herm_star z, herm_add_left]; simp; ring)
    (fun a x z => by
      rw [← Complex.coe_smul, ← herm_star _ x, ← herm_star z, herm_smul_left]; simp; ring)

theorem realForm_nondeg {e : ℝ} (he : e ≠ 0) (x : PerpendicularEmbedding.Sp P Q)
    (h : ∀ y, realForm e P Q x y = 0) : x = 0 := by
  funext i
  have h1 := h (Pi.single i 1)
  have h2 := h (Pi.single i Complex.I)
  simp only [realForm, LinearMap.mk₂_apply, mul_eq_zero, he, false_or, two_ne_zero] at h1 h2
  rcases i with i | i <;>
  · simp [PerpendicularEmbedding.herm, Pi.single_apply, apply_ite] at h1 h2
    exact Complex.ext h1 h2

theorem isAddHaar_dx (P Q : ℕ) : (PerpendicularEmbedding.dx P Q).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (by simp) (by simp)

theorem selfDual_iff : PerpendicularEmbedding.SelfDualReal ↔ ActionCoordinates.SelfDualMeasures := by
  refine forall_congr' fun e => forall_congr' fun he => and_congr ?_ ?_
  · have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
    refine forall_congr' fun P => forall_congr' fun Q => ?_
    rw [dx_eq, ← selfDual_iff_unique e ActionCoordinates.bil (realForm e P Q)
      (fun x y => by rw [bil_eq]; rfl)
      (fun x y => by
        simp only [realForm, LinearMap.mk₂_apply]; rw [← herm_star x y]; simp)
      (realForm_nondeg he0) _ (isAddHaar_dx P Q)]
    simp only [bil_eq]
  · have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
    exact selfDual_iff_unique e (fun t s : ℝ => t * s) (e • LinearMap.mul ℝ ℝ)
      (fun x y => by simp) (fun x y => by simp [mul_comm])
      (fun x h => by simpa [he0] using h 1) _ inferInstance

theorem act_mul (g h : UpqT P Q) (x : PerpendicularEmbedding.Sp P Q) :
    PerpendicularEmbedding.act (g * h) x = PerpendicularEmbedding.act g (PerpendicularEmbedding.act h x) := by
  unfold PerpendicularEmbedding.act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : PerpendicularEmbedding.Sp P Q) : PerpendicularEmbedding.act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem ext_act {g h : UpqT P Q} (H : ∀ x, PerpendicularEmbedding.act g x = PerpendicularEmbedding.act h x) : g = h :=
  GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
    (Matrix.toLin'.injective (LinearMap.ext fun x => H x))

theorem decompose {x₀ : PerpendicularEmbedding.Sp P Q} (h0 : PerpendicularEmbedding.qf x₀ ≠ 0)
    {A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ} {j : UpqT P' Q' → UpqT P Q}
    (h : PerpendicularEmbedding.IsPerpEmb x₀ A j) (y : PerpendicularEmbedding.Sp P Q) : ∃ (u : _) (a : ℂ), A *ᵥ u + a • x₀ = y := by
  have h0' : (PerpendicularEmbedding.qf x₀ : ℂ) ≠ 0 := by exact_mod_cast h0
  obtain ⟨u, hu⟩ := (h.2.1 (y + (-(PerpendicularEmbedding.herm y x₀ / PerpendicularEmbedding.qf x₀)) • x₀)).1 (by
    rw [herm_add_left, herm_smul_left, PerpendicularEmbedding.herm_self]; field_simp; ring)
  exact ⟨u, PerpendicularEmbedding.herm y x₀ / PerpendicularEmbedding.qf x₀, by rw [hu]; simp⟩

theorem emb_mul {x₀ : PerpendicularEmbedding.Sp P Q} (h0 : PerpendicularEmbedding.qf x₀ ≠ 0)
    {A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ} {j : UpqT P' Q' → UpqT P Q}
    (h : PerpendicularEmbedding.IsPerpEmb x₀ A j) (a b : UpqT P' Q') : j (a * b) = j a * j b := by
  refine ext_act fun y => ?_
  obtain ⟨u, t, rfl⟩ := decompose h0 h y
  have lin : ∀ g : UpqT P Q, PerpendicularEmbedding.act g (A *ᵥ u + t • x₀) =
      PerpendicularEmbedding.act g (A *ᵥ u) + t • PerpendicularEmbedding.act g x₀ := fun g => by
    simp [PerpendicularEmbedding.act, Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [lin, lin, act_mul, act_mul, (h.2.2 _).1, (h.2.2 _).1, (h.2.2 _).1, (h.2.2 _).2, (h.2.2 _).2,
    (h.2.2 _).2, act_mul]

theorem isInvInvariant_cd (c : CDHaar) (P Q : ℕ) : (c.cd P Q).IsInvInvariant := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  set μ := c.cd P Q
  haveI : μ.IsHaarMeasure := c.haar P Q
  haveI := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P Q μ (c.haar P Q)
  have e : μ.inv = Measure.haarScalarFactor μ.inv μ • μ := Measure.isMulLeftInvariant_eq_smul _ _
  set k := Measure.haarScalarFactor μ.inv μ
  have e2 : μ = (k * k) • μ := by
    conv_lhs => rw [← Measure.inv_inv μ, e]
    rw [Measure.inv, Measure.map_smul, ← Measure.inv, e, smul_smul]
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : UpqT P Q)
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK1).ne'
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have e3 : ((k * k : NNReal) : ℝ≥0∞) * μ K = 1 * μ K := by
    rw [one_mul]; conv_rhs => rw [e2]
    rfl
  have e4 : k * k = 1 := by exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 e3
  have e5 : k = 1 := by
    have : (k : ℝ) * k = 1 := by exact_mod_cast e4
    have h7 : (k : ℝ) = 1 := by nlinarith [k.coe_nonneg]
    exact_mod_cast h7
  exact ⟨by rw [e, e5, one_smul]⟩

theorem lintegral_inv_cd (c : CDHaar) (f : UpqT P Q → ℝ≥0∞) :
    ∫⁻ g, f g⁻¹ ∂(c.cd P Q) = ∫⁻ g, f g ∂(c.cd P Q) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI := isInvInvariant_cd c P Q
  exact lintegral_inv_eq_self f

theorem measurable_comp_inv {f : UpqT P Q → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun g => f g⁻¹ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  exact hf.comp measurable_inv

theorem inner_eq (c : CDHaar) {x₀ : PerpendicularEmbedding.Sp P Q} (h0 : PerpendicularEmbedding.qf x₀ ≠ 0)
    {A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ} {j : UpqT P' Q' → UpqT P Q}
    (h : PerpendicularEmbedding.IsPerpEmb x₀ A j) (hr : Set.range j = {g | PerpendicularEmbedding.act g x₀ = x₀})
    {a b : UpqT P Q} (hab : PerpendicularEmbedding.act a x₀ = PerpendicularEmbedding.act b⁻¹ x₀) (f : UpqT P Q → ℝ≥0∞) :
    ∫⁻ g', f (a * j g')⁻¹ ∂(c.cd P' Q') = ∫⁻ g', f (j g' * b) ∂(c.cd P' Q') := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P' Q'
  haveI := c.haar P' Q'
  let J : UpqT P' Q' →* UpqT P Q := MonoidHom.mk' j (emb_mul h0 h)
  obtain ⟨k, hk⟩ : b * a ∈ Set.range j := by
    rw [hr]; change PerpendicularEmbedding.act (b * a) x₀ = x₀
    rw [act_mul, hab, ← act_mul, mul_inv_cancel, act_one]
  rw [← lintegral_inv_cd c (fun g' => f (j g' * b)),
    ← lintegral_mul_left_eq_self (fun g' => f (j g'⁻¹ * b)) k]
  refine lintegral_congr fun g => ?_
  have : j (k * g)⁻¹ = (j k * j g)⁻¹ := by rw [← emb_mul h0 h]; exact map_inv J _
  rw [this, hk]; group

theorem formula_iff (c : CDHaar) {β : ℝ} (hβ : β ≠ 0) {x₀ : PerpendicularEmbedding.Sp P Q} (h0 : PerpendicularEmbedding.qf x₀ = β)
    {A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ} {j : UpqT P' Q' → UpqT P Q}
    (h : PerpendicularEmbedding.IsPerpEmb x₀ A j) (hr : Set.range j = {g | PerpendicularEmbedding.act g x₀ = x₀})
    (ν : Measure (PerpendicularEmbedding.Sp P Q)) (hν : ∀ᵐ y ∂ν, PerpendicularEmbedding.qf y = β) (κ : ℝ≥0∞)
    {s t : PerpendicularEmbedding.Sp P Q → UpqT P Q} (hs : ∀ y, PerpendicularEmbedding.qf y = β → PerpendicularEmbedding.act (s y) x₀ = y)
    (ht : ∀ y, PerpendicularEmbedding.qf y = β → PerpendicularEmbedding.act (t y)⁻¹ x₀ = y) :
    (∀ f : UpqT P Q → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂(c.cd P Q) =
      κ * ∫⁻ y, (∫⁻ g', f (s y * j g') ∂(c.cd P' Q')) ∂ν) ↔
    (∀ f : UpqT P Q → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂(c.cd P Q) =
      κ * ∫⁻ y in {y | PerpendicularEmbedding.qf y = β}, (∫⁻ g', f (j g' * t y) ∂(c.cd P' Q')) ∂ν) := by
  have key : ∀ f : UpqT P Q → ℝ≥0∞, ∫⁻ y, (∫⁻ g', f (s y * j g')⁻¹ ∂(c.cd P' Q')) ∂ν =
      ∫⁻ y, (∫⁻ g', f (j g' * t y) ∂(c.cd P' Q')) ∂ν := fun f =>
    lintegral_congr_ae (hν.mono fun y hy =>
      inner_eq c (h0 ▸ hβ) h hr ((hs y hy).trans (ht y hy).symm) f)
  rw [Measure.restrict_eq_self_of_ae_mem (s := {y | PerpendicularEmbedding.qf y = β}) hν]
  constructor
  · intro H f hf
    rw [← lintegral_inv_cd c f, H _ (measurable_comp_inv hf), key]
  · intro H f hf
    rw [← lintegral_inv_cd c f, H _ (measurable_comp_inv hf), ← key (fun g => f g⁻¹)]
    simp only [inv_inv]

theorem qf_add_smul {x₀ v : PerpendicularEmbedding.Sp P Q} (hv : PerpendicularEmbedding.herm v x₀ = 0) (a : ℂ) :
    PerpendicularEmbedding.qf (v + a • x₀) = PerpendicularEmbedding.qf v + Complex.normSq a * PerpendicularEmbedding.qf x₀ := by
  have hv' : PerpendicularEmbedding.herm x₀ v = 0 := by rw [← herm_star, hv, star_zero]
  have r : ∀ x y z : PerpendicularEmbedding.Sp P Q, PerpendicularEmbedding.herm x (y + a • z) =
      PerpendicularEmbedding.herm x y + star a * PerpendicularEmbedding.herm x z := fun x y z => by
    rw [← herm_star _ x, herm_add_left, herm_smul_left, star_add, star_mul', herm_star, herm_star]
  have : (PerpendicularEmbedding.qf (v + a • x₀) : ℂ) = PerpendicularEmbedding.qf v + Complex.normSq a * PerpendicularEmbedding.qf x₀ := by
    rw [← PerpendicularEmbedding.herm_self, herm_add_left, herm_smul_left, r, r, hv, hv', PerpendicularEmbedding.herm_self,
      PerpendicularEmbedding.herm_self, ← Complex.mul_conj]
    simp; ring
  exact_mod_cast this

theorem finrank_le_of_pos {V : Type} [AddCommGroup V] [Module ℂ V] (T : V →ₗ[ℂ] PerpendicularEmbedding.Sp P Q)
    (h : ∀ v, PerpendicularEmbedding.qf (T v) ≤ 0 → v = 0) : Module.finrank ℂ V ≤ P := by
  have := LinearMap.finrank_le_finrank_of_injective
    (f := (LinearMap.funLeft ℂ ℂ (Sum.inl : Fin P → Fin P ⊕ Fin Q)).comp T)
    ((injective_iff_map_eq_zero _).2 fun v hv => h v (by
      have h1 : ∀ i, T v (Sum.inl i) = 0 := fun i => congrFun hv i
      simp only [PerpendicularEmbedding.qf, h1, map_zero, Finset.sum_const_zero, zero_sub, neg_nonpos]
      exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))
  simpa using this

theorem finrank_le_of_neg {V : Type} [AddCommGroup V] [Module ℂ V] (T : V →ₗ[ℂ] PerpendicularEmbedding.Sp P Q)
    (h : ∀ v, 0 ≤ PerpendicularEmbedding.qf (T v) → v = 0) : Module.finrank ℂ V ≤ Q := by
  have := LinearMap.finrank_le_finrank_of_injective
    (f := (LinearMap.funLeft ℂ ℂ (Sum.inr : Fin Q → Fin P ⊕ Fin Q)).comp T)
    ((injective_iff_map_eq_zero _).2 fun v hv => h v (by
      have h1 : ∀ i, T v (Sum.inr i) = 0 := fun i => congrFun hv i
      simp only [PerpendicularEmbedding.qf, h1, map_zero, Finset.sum_const_zero, sub_zero]
      exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _))
  simpa using this

theorem eq_zero_of_sum_normSq {n : ℕ} {u : Fin n → ℂ} (h : ∑ i, Complex.normSq (u i) ≤ 0) :
    u = 0 := by
  have h1 := le_antisymm h (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _] at h1
  funext i
  exact Complex.normSq_eq_zero.1 (h1 i (Finset.mem_univ i))

def inlMap (P Q : ℕ) : (Fin P → ℂ) →ₗ[ℂ] PerpendicularEmbedding.Sp P Q where
  toFun u := Sum.elim u 0
  map_add' u v := by funext i; rcases i with i | i <;> simp
  map_smul' a v := by funext i; rcases i with i | i <;> simp

def inrMap (P Q : ℕ) : (Fin Q → ℂ) →ₗ[ℂ] PerpendicularEmbedding.Sp P Q where
  toFun u := Sum.elim 0 u
  map_add' u v := by funext i; rcases i with i | i <;> simp
  map_smul' a v := by funext i; rcases i with i | i <;> simp

theorem signature_perp {x₀ : PerpendicularEmbedding.Sp P Q}
    {A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ} {j : UpqT P' Q' → UpqT P Q}
    (h : PerpendicularEmbedding.IsPerpEmb x₀ A j) :
    (PerpendicularEmbedding.qf x₀ = 1 → P = P' + 1 ∧ Q = Q') ∧ (PerpendicularEmbedding.qf x₀ = -1 → P = P' ∧ Q = Q' + 1) := by
  let T : (PerpendicularEmbedding.Sp P' Q' × ℂ) →ₗ[ℂ] PerpendicularEmbedding.Sp P Q :=
    (Matrix.toLin' A).coprod (LinearMap.toSpanSingleton ℂ _ x₀)
  have hq : ∀ u, PerpendicularEmbedding.qf (A *ᵥ u) = PerpendicularEmbedding.qf u := fun u => by
    have := h.1 u u
    rw [PerpendicularEmbedding.herm_self, PerpendicularEmbedding.herm_self] at this
    exact_mod_cast this
  have hT : ∀ u a, PerpendicularEmbedding.qf (T (u, a)) = PerpendicularEmbedding.qf u + Complex.normSq a * PerpendicularEmbedding.qf x₀ :=
    fun u a => by
      rw [← hq u]; exact qf_add_smul ((h.2.1 _).2 ⟨u, rfl⟩) a
  have hdim : PerpendicularEmbedding.qf x₀ ≠ 0 → P + Q ≤ P' + Q' + 1 := fun h0 => by
    have := LinearMap.finrank_le_finrank_of_surjective (f := T) fun y => by
      obtain ⟨u, a, hu⟩ := decompose h0 h y
      exact ⟨(u, a), hu⟩
    simpa using this
  have l : ∀ u, PerpendicularEmbedding.qf (inlMap P' Q' u) = ∑ i, Complex.normSq (u i) := fun u => by
    simp [PerpendicularEmbedding.qf, inlMap]
  have r : ∀ u, PerpendicularEmbedding.qf (inrMap P' Q' u) = -∑ i, Complex.normSq (u i) := fun u => by
    simp [PerpendicularEmbedding.qf, inrMap]
  have hP : P' ≤ P := by
    simpa using finrank_le_of_pos ((Matrix.toLin' A).comp (inlMap P' Q')) fun u hu =>
      eq_zero_of_sum_normSq (by rw [← l, ← hq]; exact hu)
  have hQ : Q' ≤ Q := by
    simpa using finrank_le_of_neg ((Matrix.toLin' A).comp (inrMap P' Q')) fun u hu =>
      eq_zero_of_sum_normSq (by rw [← neg_nonneg, ← r, ← hq]; exact hu)
  constructor
  · intro h1
    have h2 := hdim (by rw [h1]; exact one_ne_zero)
    have h3 : P' + 1 ≤ P := by
      simpa using finrank_le_of_pos (T.comp ((inlMap P' Q').prodMap LinearMap.id)) fun v hv => by
        have h4 : PerpendicularEmbedding.qf (T (inlMap P' Q' v.1, v.2)) ≤ 0 := hv
        rw [hT, l, h1, mul_one] at h4
        have h5 := Complex.normSq_nonneg v.2
        have h6 : 0 ≤ ∑ i, Complex.normSq (v.1 i) :=
          Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
        exact Prod.ext (eq_zero_of_sum_normSq (by linarith))
          (Complex.normSq_eq_zero.1 (by linarith))
    omega
  · intro h1
    have h2 := hdim (by rw [h1]; norm_num)
    have h3 : Q' + 1 ≤ Q := by
      simpa using finrank_le_of_neg (T.comp ((inrMap P' Q').prodMap LinearMap.id)) fun v hv => by
        have h4 : 0 ≤ PerpendicularEmbedding.qf (T (inrMap P' Q' v.1, v.2)) := hv
        rw [hT, r, h1] at h4
        have h5 := Complex.normSq_nonneg v.2
        have h6 : 0 ≤ ∑ i, Complex.normSq (v.1 i) :=
          Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
        exact Prod.ext (eq_zero_of_sum_normSq (by linarith))
          (Complex.normSq_eq_zero.1 (by linarith))
    omega

def PointClauses (c : CDHaar) (P Q P' Q' : ℕ) (β : ℝ) (x₀ : ActionCoordinates.Wsp P Q) : Prop :=
  (∀ y : ActionCoordinates.Wsp P Q, ActionCoordinates.qf y = β → ∃ g : UpqT P Q, ActionCoordinates.act g⁻¹ x₀ = y) ∧
  (∃ (j : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
    ActionCoordinates.IsPerpFrame x₀ j ι) ∧
  ∀ (j : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
    ActionCoordinates.IsPerpFrame x₀ j ι →
      Set.range ι = {g | ActionCoordinates.act g x₀ = x₀} ∧
      ∀ (fib : ℝ → Measure (ActionCoordinates.Wsp P Q)), ActionCoordinates.IsDxDq β fib →
        ∀ s : ActionCoordinates.Wsp P Q → UpqT P Q, (∀ y, ActionCoordinates.qf y = β → ActionCoordinates.act (s y)⁻¹ x₀ = y) →
          ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
            ∫⁻ g, f g ∂(c.cd P Q) =
              (ActionCoordinates.cM (P + Q))⁻¹ *
                ∫⁻ y in {y | ActionCoordinates.qf y = β}, (∫⁻ g', f (ι g' * s y) ∂(c.cd P' Q')) ∂(fib β)

theorem quotFormula_iff (c : CDHaar) (P Q P' Q' : ℕ) {β : ℝ} (hβ : β ≠ 0) :
    PerpendicularEmbedding.QuotFormula c P Q P' Q' β ↔
      ∀ x₀ : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x₀ = β → PointClauses c P Q P' Q' β x₀ := by
  unfold PointClauses
  rw [qf_eq]
  refine forall_congr' fun x₀ => forall_congr' fun h0 => ?_
  constructor
  · rintro ⟨⟨⟨A, j⟩, hA⟩, H⟩
    refine ⟨fun y hy => ?_, ⟨_, j, (isPerpFrame_iff x₀ A j).2 hA⟩, fun A' ι hι => ?_⟩
    · obtain ⟨-, ⟨fib, hfib⟩, H2⟩ := H _ hA
      obtain ⟨⟨s, hs⟩, -⟩ := H2 fib hfib
      exact ⟨(s y)⁻¹, by rw [inv_inv]; exact hs.2 y hy⟩
    · have hι' := (isPerpEmb_iff x₀ A' ι).2 hι
      obtain ⟨hr, ⟨fib, hfib⟩, H2⟩ := H (_, ι) hι'
      obtain ⟨⟨s, hs⟩, H3⟩ := H2 fib hfib
      refine ⟨hr, fun fib' hfib' t ht => ?_⟩
      rw [fib_eq hβ hfib hfib']
      exact (formula_iff c hβ h0 hι' hr _ (ae_qf hfib β) _ hs.2 ht).1 (H3 s hs)
  · rintro ⟨-, ⟨A, j, hA⟩, H⟩
    refine ⟨⟨(_, j), (isPerpEmb_iff x₀ A j).2 hA⟩, ?_⟩
    rintro ⟨A', ι⟩ hι
    obtain ⟨hr, H2⟩ := H _ ι ((isPerpFrame_iff x₀ A' ι).2 hι)
    refine ⟨hr, exists_isDxDq P Q, fun fib hfib => ⟨GlobalTheory.T.exists_borelSection_unitary_orbit_quadric P Q β x₀ hβ h0, fun s hs => ?_⟩⟩
    have ht : ∀ y, PerpendicularEmbedding.qf y = β → PerpendicularEmbedding.act ((s y)⁻¹)⁻¹ x₀ = y := fun y hy => by
      rw [inv_inv]; exact hs.2 y hy
    exact (formula_iff c hβ h0 hι hr _ (ae_qf hfib β) _ hs.2 ht).2
      (H2 fib (isDxDq_local hfib β) _ ht)

theorem quotient_iff : PerpendicularEmbedding.CompactDualQuotient ↔ ActionCoordinates.QuotientMeasure := by
  constructor
  · intro h P Q β hβ x₀ h0
    obtain ⟨c₀⟩ := GlobalTheory.CompactDualExists.nonempty_cdHaar
    have hq0 : PerpendicularEmbedding.qf x₀ = β := by rw [← qf_eq]; exact h0
    have nn : ∀ {n : ℕ} (u : Fin n → ℂ), 0 ≤ ∑ i, Complex.normSq (u i) := fun u =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    rcases hβ with rfl | rfl
    · obtain _ | P := P
      · have := nn fun i => x₀ (Sum.inr i)
        simp only [PerpendicularEmbedding.qf, Finset.univ_eq_empty, Finset.sum_empty] at hq0
        linarith
      have H := fun c => (quotFormula_iff c _ _ _ _ one_ne_zero).1 (h c P Q).1 x₀ h0
      obtain ⟨h1, ⟨j, ι, h2⟩, h3⟩ := H c₀
      refine ⟨h1, ⟨P, Q, j, ι, fun _ => ⟨rfl, rfl⟩, fun e => by norm_num at e, h2⟩, ?_⟩
      intro P' Q' j ι hι
      obtain ⟨e1, e2⟩ := (signature_perp ((isPerpEmb_iff x₀ j ι).2 hι)).1 hq0
      obtain rfl : P = P' := by omega
      subst e2
      exact ⟨(h3 j ι hι).1, fun c => ((H c).2.2 j ι hι).2⟩
    · obtain _ | Q := Q
      · have := nn fun i => x₀ (Sum.inl i)
        simp only [PerpendicularEmbedding.qf, Finset.univ_eq_empty, Finset.sum_empty] at hq0
        linarith
      have H := fun c => (quotFormula_iff c _ _ _ _ (by norm_num)).1 (h c P Q).2 x₀ h0
      obtain ⟨h1, ⟨j, ι, h2⟩, h3⟩ := H c₀
      refine ⟨h1, ⟨P, Q, j, ι, fun e => by norm_num at e, fun _ => ⟨rfl, rfl⟩, h2⟩, ?_⟩
      intro P' Q' j ι hι
      obtain ⟨e1, e2⟩ := (signature_perp ((isPerpEmb_iff x₀ j ι).2 hι)).2 hq0
      obtain rfl : Q = Q' := by omega
      subst e1
      exact ⟨(h3 j ι hι).1, fun c => ((H c).2.2 j ι hι).2⟩
  · intro h c P Q
    constructor
    · refine (quotFormula_iff c _ _ _ _ one_ne_zero).2 fun x₀ h0 => ?_
      obtain ⟨h1, ⟨P', Q', j, ι, e, -, h2⟩, h3⟩ := h _ _ 1 (Or.inl rfl) x₀ h0
      obtain ⟨e1, rfl⟩ := e rfl
      obtain rfl : P' = P := by omega
      exact ⟨h1, ⟨j, ι, h2⟩, fun j ι hι => ⟨(h3 _ _ j ι hι).1, (h3 _ _ j ι hι).2 c⟩⟩
    · refine (quotFormula_iff c _ _ _ _ (by norm_num)).2 fun x₀ h0 => ?_
      obtain ⟨h1, ⟨P', Q', j, ι, -, e, h2⟩, h3⟩ := h _ _ (-1) (Or.inr rfl) x₀ h0
      obtain ⟨rfl, e1⟩ := e rfl
      obtain rfl : Q' = Q := by omega
      exact ⟨h1, ⟨j, ι, h2⟩, fun j ι hι => ⟨(h3 _ _ j ι hι).1, (h3 _ _ j ι hι).2 c⟩⟩

theorem typings_agree :
    (PerpendicularEmbedding.SelfDualReal ↔ ActionCoordinates.SelfDualMeasures) ∧
    (PerpendicularEmbedding.SphereMass ↔ ActionCoordinates.SphereVolume) ∧
    (PerpendicularEmbedding.CompactDualQuotient ↔ ActionCoordinates.QuotientMeasure) ∧
    (PerpendicularEmbedding.SelfDualReal ∧ PerpendicularEmbedding.SphereMass ∧ PerpendicularEmbedding.CompactDualQuotient ↔
      ActionCoordinates.RealPlaceMeasures) :=
  ⟨selfDual_iff, sphere_iff, quotient_iff,
    and_congr selfDual_iff (and_congr sphere_iff quotient_iff)⟩

end GlobalTheory.RealPlaceCompare
