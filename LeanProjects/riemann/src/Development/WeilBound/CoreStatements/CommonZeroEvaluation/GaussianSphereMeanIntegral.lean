import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianMatrixMeasurePosFinite
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace ModelDimension.GSph

noncomputable section

theorem transfer {Ω S X : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace X]
    (γ : Measure Ω) [IsFiniteMeasure γ] (ν : Measure S) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ Set.univ ≠ 0) {φ : Ω → X} (hφ : Measurable φ) {T : S × X → X} (hT : Measurable T)
    (hmap : γ.map φ = (ν.prod μ).map T) {F : X → ℝ} (hF : AEStronglyMeasurable F (γ.map φ))
    (hinv : ∀ᵐ s ∂ν, ∀ u, F (T (s, u)) = F u) (hint : Integrable F μ) :
    Integrable (fun x => F (φ x)) γ ∧
      ∫ x, F (φ x) ∂γ = (γ Set.univ).toReal * ⨍ u, F u ∂μ := by
  have hmass : γ Set.univ = ν Set.univ * μ Set.univ := by
    have h1 : γ Set.univ = (γ.map φ) Set.univ := by
      rw [Measure.map_apply hφ MeasurableSet.univ, Set.preimage_univ]
    rw [h1, hmap, Measure.map_apply hT MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod]
  have hνfin : ν Set.univ ≠ ⊤ := by
    have h2 : ν Set.univ * μ Set.univ ≠ ⊤ := by rw [← hmass]; exact measure_ne_top γ _
    exact (ENNReal.lt_top_of_mul_ne_top_left h2 hμ).ne
  haveI : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.2 hνfin⟩
  have hF' : AEStronglyMeasurable F ((ν.prod μ).map T) := hmap ▸ hF
  have hFT : AEStronglyMeasurable (fun p => F (T p)) (ν.prod μ) := hF'.comp_measurable hT
  have hintT : Integrable (fun p => F (T p)) (ν.prod μ) := by
    rw [integrable_prod_iff hFT]
    constructor
    · filter_upwards [hinv] with s hs
      simp only [hs]
      exact hint
    · refine (integrable_const (∫ u, ‖F u‖ ∂μ)).congr ?_
      filter_upwards [hinv] with s hs
      simp only [hs]
  have hintMap : Integrable F ((ν.prod μ).map T) := (integrable_map_measure hF' hT.aemeasurable).2 hintT
  refine ⟨?_, ?_⟩
  · refine (integrable_map_measure hF hφ.aemeasurable).1 ?_
    rw [hmap]; exact hintMap
  · rw [← integral_map hφ.aemeasurable hF, hmap, integral_map hT.aemeasurable hF',
      integral_prod _ hintT]
    have h3 : (fun s => ∫ u, F (T (s, u)) ∂μ) =ᵐ[ν] fun _ => ∫ u, F u ∂μ := by
      filter_upwards [hinv] with s hs
      simp only [hs]
    rw [integral_congr_ae h3, integral_const, smul_eq_mul, average_eq, smul_eq_mul, hmass,
      ENNReal.toReal_mul]
    have h4 : (μ Set.univ).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hμ, measure_ne_top μ _⟩
    simp only [measureReal_def]
    field_simp

variable {n e : ℕ}

def sc (c : Fin e → ℝ) : (Fin e × Fin n → ℂ) →ₗ[ℂ] (Fin e × Fin n → ℂ) where
  toFun u := fun ij => (c ij.1 : ℂ) * u ij
  map_add' u v := by funext ij; simp [mul_add]
  map_smul' a u := by funext ij; simp [mul_left_comm]

theorem sc_apply (c : Fin e → ℝ) (u : Fin e × Fin n → ℂ) (ij : Fin e × Fin n) :
    sc c u ij = (c ij.1 : ℂ) * u ij := rfl

theorem sc_surjective {c : Fin e → ℝ} (hc : ∀ i, 0 < c i) :
    Function.Surjective (sc (n := n) c) := by
  intro v
  refine ⟨fun ij => v ij / (c ij.1 : ℂ), ?_⟩
  funext ij
  have hne : (c ij.1 : ℂ) ≠ 0 := by exact_mod_cast (hc ij.1).ne'
  simp only [sc_apply]
  field_simp

def rowN (h : HermNorm n) (u : Fin e × Fin n → ℂ) (i : Fin e) : ℝ := h.norm fun j => u (i, j)

theorem rowN_nonneg (h : HermNorm n) (u : Fin e × Fin n → ℂ) (i : Fin e) : 0 ≤ rowN h u i :=
  Real.sqrt_nonneg _

theorem continuous_rowN (h : HermNorm n) (i : Fin e) :
    Continuous fun u : Fin e × Fin n → ℂ => rowN h u i := continuous_hermNorm_group h i

theorem rowN_sc (h : HermNorm n) {c : Fin e → ℝ} (hc : ∀ i, 0 < c i) (u : Fin e × Fin n → ℂ)
    (i : Fin e) : rowN h (sc c u) i = c i * rowN h u i := by
  unfold rowN HermNorm.norm
  have h1 : (fun j => sc c u (i, j)) = (c i : ℂ) • fun j => u (i, j) := by
    funext j; simp [sc_apply]
  rw [h1, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (by positivity), Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sqrt_sq (hc i).le]

theorem nrm_sc (h : HermNorm n) {c : Fin e → ℝ} (hc : ∀ i, 0 < c i) (u : Fin e × Fin n → ℂ) :
    nrmGroups h e (sc c u) = nrmGroups h e u := by
  funext ij
  have h1 : (h.norm fun j => sc c u (ij.1, j)) = c ij.1 * h.norm fun j => u (ij.1, j) :=
    rowN_sc h hc u ij.1
  simp only [nrmGroups]
  rw [h1, sc_apply]
  have hne : (c ij.1 : ℂ) ≠ 0 := by exact_mod_cast (hc ij.1).ne'
  push_cast
  rw [mul_inv, mul_assoc, ← mul_assoc _ (c ij.1 : ℂ), mul_comm _ (c ij.1 : ℂ), ← mul_assoc,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem measurable_sc (c : Fin e → ℝ) : Measurable (sc (n := n) c) :=
  (LinearMap.continuous_of_finiteDimensional _).measurable

theorem map_sc {c : Fin e → ℝ} (hc : ∀ i, 0 < c i) :
    ∃ d : ℝ≥0∞, 0 < d ∧ (volume : Measure (Fin e × Fin n → ℂ)).map (sc c) = d • volume := by
  classical
  set f : (Fin e × Fin n → ℂ) →ₗ[ℝ] (Fin e × Fin n → ℂ) := (sc (n := n) c).restrictScalars ℝ with hf
  have hinj : Function.Injective f := by
    intro u v huv
    funext ij
    have h1 := congrFun huv ij
    simp only [hf, LinearMap.coe_restrictScalars, sc_apply] at h1
    have hc' : (c ij.1 : ℂ) ≠ 0 := by exact_mod_cast (hc ij.1).ne'
    exact mul_left_cancel₀ hc' h1
  have hsurj : Function.Surjective f := sc_surjective hc
  have hdet : LinearMap.det f ≠ 0 :=
    ((LinearMap.isUnit_iff_isUnit_det f).1 ((Module.End.isUnit_iff f).2 ⟨hinj, hsurj⟩)).ne_zero
  refine ⟨ENNReal.ofReal |(LinearMap.det f)⁻¹|, ?_, ?_⟩
  · exact ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hdet))
  · exact Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin e × Fin n → ℂ)) hdet

theorem aesm (h : HermNorm n) (G : (Fin e × Fin n → ℂ) → ℝ)
    (hG : AEStronglyMeasurable (fun u => G (nrmGroups h e u)) (volume.restrict (ballProd h e))) :
    AEStronglyMeasurable (fun u => G (nrmGroups h e u)) volume := by
  have hcov : ∀ u : Fin e × Fin n → ℂ, ∃ m : ℕ,
      sc (n := n) (fun _ => (1 : ℝ) / (m + 1)) u ∈ ballProd h e := by
    intro u
    obtain ⟨m, hm⟩ := exists_nat_gt (∑ i, rowN h u i)
    refine ⟨m, ?_⟩
    simp only [ballProd, Set.mem_setOf_eq]
    intro i
    have h1 := rowN_sc h (c := fun _ => (1 : ℝ) / (m + 1)) (fun _ => by positivity) u i
    change rowN h (sc (fun _ => (1 : ℝ) / (m + 1)) u) i < 1
    rw [h1]
    have hle : rowN h u i ≤ ∑ i, rowN h u i :=
      Finset.single_le_sum (fun j _ => rowN_nonneg h u j) (Finset.mem_univ i)
    have hpos : (0 : ℝ) < m + 1 := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_lt_one hpos]
    linarith
  have hF : ∀ m : ℕ, AEStronglyMeasurable (fun u => G (nrmGroups h e u))
      (volume.restrict (sc (n := n) (fun _ => (1 : ℝ) / (m + 1)) ⁻¹' ballProd h e)) := by
    intro m
    have hc : ∀ i : Fin e, (0 : ℝ) < (fun _ => (1 : ℝ) / (m + 1)) i := fun _ => by positivity
    obtain ⟨d, hd, hmap⟩ := map_sc (n := n) hc
    have hq : Measure.QuasiMeasurePreserving (sc (n := n) (fun _ => (1 : ℝ) / (m + 1)))
        (volume.restrict (sc (n := n) (fun _ => (1 : ℝ) / (m + 1)) ⁻¹' ballProd h e))
        (volume.restrict (ballProd h e)) := by
      refine ⟨measurable_sc _, ?_⟩
      rw [← Measure.restrict_map (measurable_sc _) (isOpen_ballProd h e).measurableSet, hmap,
        Measure.restrict_smul]
      exact Measure.smul_absolutelyContinuous
    have h2 := hG.comp_quasiMeasurePreserving hq
    have heq : (fun u => G (nrmGroups h e u)) =
        (fun u => G (nrmGroups h e u)) ∘ sc (n := n) (fun _ => (1 : ℝ) / (m + 1)) := by
      funext u
      simp only [Function.comp, nrm_sc h hc u]
    rw [heq]
    exact h2
  have hU : (⋃ m : ℕ, sc (n := n) (fun _ => (1 : ℝ) / (m + 1)) ⁻¹' ballProd h e) = Set.univ := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
    exact hcov u
  rw [← Measure.restrict_univ (μ := volume), ← hU]
  exact aestronglyMeasurable_iUnion_iff.2 hF

def ex1 : Measure ℝ :=
  (volume.restrict (Set.Ioi 0)).withDensity fun s => ENNReal.ofReal (Real.exp (-s))

theorem exponential_measure_Ioi {t : ℝ} (ht : 0 ≤ t) : ex1 (Set.Ioi t) = ENNReal.ofReal (Real.exp (-t)) := by
  rw [ex1, withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.Ioi_inter_Ioi, sup_eq_left.2 ht,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi t)
      (ae_of_all _ fun x => (Real.exp_pos _).le), integral_exp_neg_Ioi]

instance exponential_measure_finite : IsFiniteMeasure ex1 := ⟨by
  rw [ex1, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (integrableOn_exp_neg_Ioi 0).lintegral_lt_top⟩

theorem exponential_measure_pos_ae : ∀ᵐ s ∂ex1, 0 < s :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

def exP (e : ℕ) : Measure (Fin e → ℝ) := Measure.pi fun _ => ex1

instance isFiniteMeasure_piExponential : IsFiniteMeasure (exP e) := by
  unfold exP
  infer_instance

theorem ae_pos_piExponential : ∀ᵐ s ∂(exP e), ∀ i, 0 < s i := by
  unfold exP
  rw [ae_all_iff]
  intro i
  exact (Measure.tendsto_eval_ae_ae (i := i)).eventually exponential_measure_pos_ae

def rowGauss (h : HermNorm n) (u : Fin e × Fin n → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ i, rowN h u i ^ 2))

theorem measurable_rowGauss (h : HermNorm n) : Measurable (rowGauss (e := e) h) := by
  unfold rowGauss
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  refine Measurable.neg (Finset.measurable_sum _ fun i _ => ?_)
  exact ((continuous_rowN h i).measurable).pow_const 2

def under (h : HermNorm n) (e : ℕ) : Set ((Fin e → ℝ) × (Fin e × Fin n → ℂ)) :=
  {p | ∀ i, rowN h p.2 i ^ 2 < p.1 i}

theorem isOpen_under (h : HermNorm n) : IsOpen (under h e) := by
  have e1 : under h e = ⋂ i, {p | rowN h p.2 i ^ 2 < p.1 i} := by
    ext p
    simp [under]
  rw [e1]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (((continuous_rowN h i).comp continuous_snd).pow 2)
      ((continuous_apply i).comp continuous_fst)

theorem piExponential_preimage_under (h : HermNorm n) (u : Fin e × Fin n → ℂ) :
    exP e ((fun s => (s, u)) ⁻¹' under h e) = rowGauss h u := by
  have hpre : (fun s => (s, u)) ⁻¹' under h e = Set.univ.pi fun i => Set.Ioi (rowN h u i ^ 2) := by
    ext s; simp [under]
  rw [hpre, exP, Measure.pi_pi]
  simp_rw [exponential_measure_Ioi (sq_nonneg _)]
  rw [rowGauss, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
    Finset.sum_neg_distrib]

def scT (p : (Fin e → ℝ) × (Fin e × Fin n → ℂ)) : Fin e × Fin n → ℂ :=
  sc (fun i => √(p.1 i)) p.2

theorem measurable_scT : Measurable (scT (n := n) (e := e)) := by
  unfold scT
  refine measurable_pi_lambda _ fun ij => ?_
  simp only [sc_apply]
  refine Measurable.mul ?_ ?_
  · exact Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp ((measurable_pi_apply ij.1).comp measurable_fst))
  · exact (measurable_pi_apply ij).comp measurable_snd

def wt (h : HermNorm n) (s : Fin e → ℝ) : ℝ≥0∞ :=
  volume (Prod.mk s ⁻¹' under h e) / volume (ballProd h e)

theorem measurable_wt (h : HermNorm n) : Measurable (wt (e := e) h) :=
  (measurable_measure_prodMk_left (isOpen_under h).measurableSet).div_const _

theorem wt_mul (h : HermNorm n) {s : Fin e → ℝ} (hs : ∀ i, 0 < s i) {A : Set (Fin e × Fin n → ℂ)}
    (hA : MeasurableSet A) :
    wt h s * (volume.restrict (ballProd h e)) (Prod.mk s ⁻¹' (scT ⁻¹' A)) =
      volume (Prod.mk s ⁻¹' (under h e ∩ Prod.snd ⁻¹' A)) := by
  classical
  set c : Fin e → ℝ := fun i => √(s i) with hcd
  have hc : ∀ i, 0 < c i := fun i => Real.sqrt_pos.2 (hs i)
  set c' : Fin e → ℝ := fun i => (c i)⁻¹ with hcd'
  have hc' : ∀ i, 0 < c' i := fun i => inv_pos.2 (hc i)
  have hcomp : ∀ u, sc (n := n) c (sc c' u) = u := by
    intro u
    funext ij
    simp only [sc_apply, hcd', ← mul_assoc, Complex.ofReal_inv]
    rw [mul_inv_cancel₀ (by exact_mod_cast (hc ij.1).ne'), one_mul]
  have hslice : Prod.mk s ⁻¹' under h e = sc (n := n) c' ⁻¹' ballProd h e := by
    ext u
    show (∀ i, rowN h u i ^ 2 < s i) ↔ ∀ i, rowN h (sc c' u) i < 1
    refine forall_congr' fun i => ?_
    rw [rowN_sc h hc' u i, ← Real.lt_sqrt (rowN_nonneg h u i)]
    show rowN h u i < c i ↔ (c i)⁻¹ * rowN h u i < 1
    rw [inv_mul_lt_iff₀ (hc i), mul_one]
  have hpre : Prod.mk s ⁻¹' (under h e ∩ Prod.snd ⁻¹' A) =
      sc (n := n) c' ⁻¹' (ballProd h e ∩ sc c ⁻¹' A) := by
    rw [Set.preimage_inter, hslice, Set.preimage_inter]
    congr 1
    ext u
    simp [hcomp]
  have hmeasA : MeasurableSet (sc (n := n) c ⁻¹' A) := measurable_sc c hA
  have hball : MeasurableSet (ballProd h e) := (isOpen_ballProd h e).measurableSet
  obtain ⟨d, -, hd⟩ := map_sc (n := n) hc'
  have hvol : ∀ X, MeasurableSet X → volume (sc (n := n) c' ⁻¹' X) = d * volume X := by
    intro X hX
    have h1 := congrArg (fun μ : Measure (Fin e × Fin n → ℂ) => μ X) hd
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    rw [Measure.map_apply (measurable_sc c') hX] at h1
    exact h1
  have hwt : wt h s = d := by
    rw [wt, hslice, hvol _ hball]
    exact ENNReal.mul_div_cancel_right (volume_ballProd_pos h e).ne' (volume_ballProd_lt_top h e).ne
  rw [hwt, hpre, hvol _ (hball.inter hmeasA)]
  change d * (volume.restrict (ballProd h e)) (sc (n := n) c ⁻¹' A) = _
  rw [Measure.restrict_apply hmeasA, Set.inter_comm]

theorem layer (h : HermNorm n) :
    (volume : Measure (Fin e × Fin n → ℂ)).withDensity (rowGauss h) =
      (((exP e).withDensity (wt h)).prod (volume.restrict (ballProd h e))).map scT := by
  ext A hA
  have hm : MeasurableSet (under h e ∩ Prod.snd ⁻¹' A) :=
    (isOpen_under h).measurableSet.inter (measurable_snd hA)
  rw [Measure.map_apply measurable_scT hA, Measure.prod_apply (measurable_scT hA),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_wt h)
      (measurable_measure_prodMk_left (measurable_scT hA))]
  have h1 : ∫⁻ s, wt h s * (volume.restrict (ballProd h e)) (Prod.mk s ⁻¹' (scT ⁻¹' A))
      ∂(exP e) = ∫⁻ s, volume (Prod.mk s ⁻¹' (under h e ∩ Prod.snd ⁻¹' A)) ∂(exP e) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_pos_piExponential (e := e)] with s hs
    exact wt_mul h hs hA
  simp only [Pi.mul_apply]
  rw [h1, ← Measure.prod_apply hm, Measure.prod_apply_symm hm, withDensity_apply _ hA,
    ← lintegral_indicator hA]
  refine lintegral_congr fun u => ?_
  by_cases hu : u ∈ A
  · rw [Set.indicator_of_mem hu, ← piExponential_preimage_under]
    congr 1
    ext s
    simp [hu]
  · rw [Set.indicator_of_notMem hu]
    have e1 : (fun s => (s, u)) ⁻¹' (under h e ∩ Prod.snd ⁻¹' A) = ∅ := by
      ext s
      simp [hu]
    rw [e1, measure_empty]

def splitL (h : HermNorm n) (e : ℕ) :
    (Fin (e + 1) → Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) × (Fin e × Fin n → ℂ) where
  toFun π := (π 0, coefRows h π)
  map_add' π ρ := by
    refine Prod.ext rfl (funext fun ij => ?_)
    simp [coefRows, Matrix.mulVec_add]
  map_smul' a π := by
    refine Prod.ext rfl (funext fun ij => ?_)
    simp [coefRows, Matrix.mulVec_smul]

theorem splitL_surjective (h : HermNorm n) : Function.Surjective (splitL h e) := by
  rintro ⟨x, w⟩
  refine ⟨Fin.cons x fun i => h.mat *ᵥ fun j => w (i, j), ?_⟩
  simp only [splitL, LinearMap.coe_mk, AddHom.coe_mk, Fin.cons_zero, Prod.mk.injEq, true_and]
  funext ij
  simp only [coefRows, Fin.cons_succ, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det,
    Matrix.one_mulVec]

theorem measurable_splitL (h : HermNorm n) : Measurable (splitL h e) :=
  (LinearMap.continuous_of_finiteDimensional _).measurable

theorem measurable_coefRows (h : HermNorm n) :
    Measurable (coefRows (e := e) h) := measurable_snd.comp (measurable_splitL h)

theorem rowN_coefRows (h : HermNorm n) (π : Fin (e + 1) → Fin n → ℂ) (i : Fin e) :
    rowN h (coefRows h π) i ^ 2 = ∑ j, ‖π i.succ j‖ ^ 2 := by
  unfold rowN HermNorm.norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  have h1 : (h.mat *ᵥ fun j => coefRows h π (i, j)) = π i.succ := by
    have h2 : (fun j => coefRows h π (i, j)) = h.mat⁻¹ *ᵥ π i.succ := by funext j; rfl
    rw [h2, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h.isUnit_det, Matrix.one_mulVec]
  rw [h1]

theorem map_coefRows (h : HermNorm n) : ∃ a : ℝ≥0∞,
    (gaussM (e + 1) n).map (coefRows h) =
      a • (volume : Measure (Fin e × Fin n → ℂ)).withDensity (rowGauss h) := by
  classical
  have hinj : Function.Injective (splitL h e) := by
    intro π ρ hπρ
    have h0 : π 0 = ρ 0 := congrArg Prod.fst hπρ
    have h1 : coefRows h π = coefRows h ρ := congrArg Prod.snd hπρ
    funext i
    induction i using Fin.cases with
    | zero => exact h0
    | succ i' =>
      have hrow : h.mat⁻¹ *ᵥ π i'.succ = h.mat⁻¹ *ᵥ ρ i'.succ := by
        funext j
        exact congrFun h1 (i', j)
      have h2 := congrArg (fun v => h.mat *ᵥ v) hrow
      simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h.isUnit_det] using h2
  let Ψl : (Fin (e + 1) → Fin n → ℂ) ≃ₗ[ℝ] (Fin n → ℂ) × (Fin e × Fin n → ℂ) :=
    LinearEquiv.ofBijective ((splitL h e).restrictScalars ℝ) ⟨hinj, splitL_surjective h⟩
  let Ψ := Ψl.toContinuousLinearEquiv
  have hΨ : ∀ π, Ψ π = (π 0, coefRows h π) := fun π => rfl
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  haveI : (volume : Measure (Fin e × Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  haveI : (volume : Measure ((Fin n → ℂ) × (Fin e × Fin n → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI : (Measure.map Ψ (volume : Measure (Fin (e + 1) → Fin n → ℂ))).IsAddHaarMeasure :=
    Ψ.isAddHaarMeasure_map volume
  have hc := Measure.isAddLeftInvariant_eq_smul
    (Measure.map Ψ (volume : Measure (Fin (e + 1) → Fin n → ℂ)))
    (volume : Measure ((Fin n → ℂ) × (Fin e × Fin n → ℂ)))
  set c := (Measure.map Ψ (volume : Measure (Fin (e + 1) → Fin n → ℂ))).addHaarScalarFactor
    (volume : Measure ((Fin n → ℂ) × (Fin e × Fin n → ℂ)))
  have hg0 : Measurable fun x : Fin n → ℂ => ENNReal.ofReal (Real.exp (-∑ j, ‖x j‖ ^ 2)) := by
    fun_prop
  refine ⟨(c : ℝ≥0∞) * ∫⁻ x : Fin n → ℂ, ENNReal.ofReal (Real.exp (-∑ j, ‖x j‖ ^ 2)), ?_⟩
  ext A hA
  have hmA : MeasurableSet (coefRows h ⁻¹' A) := measurable_coefRows h hA
  rw [Measure.map_apply (measurable_coefRows h) hA, Measure.smul_apply, withDensity_apply _ hA,
    smul_eq_mul, gaussM, withDensity_apply _ hmA, ← lintegral_indicator hmA]
  have key : ∀ π, (coefRows h ⁻¹' A).indicator matGauss π =
      (fun p : (Fin n → ℂ) × (Fin e × Fin n → ℂ) =>
        ENNReal.ofReal (Real.exp (-∑ j, ‖p.1 j‖ ^ 2)) * A.indicator (rowGauss h) p.2) (Ψ π) := by
    intro π
    rw [hΨ]
    simp only [Set.indicator, Set.mem_preimage]
    split_ifs with hπ
    · simp only [matGauss, rowGauss, rowN_coefRows, Fin.sum_univ_succ]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    · simp
  simp_rw [key]
  have hF : Measurable fun p : (Fin n → ℂ) × (Fin e × Fin n → ℂ) =>
      ENNReal.ofReal (Real.exp (-∑ j, ‖p.1 j‖ ^ 2)) * A.indicator (rowGauss h) p.2 :=
    (hg0.comp measurable_fst).mul (((measurable_rowGauss h).indicator hA).comp measurable_snd)
  have hprod := lintegral_prod_mul (μ := (volume : Measure (Fin n → ℂ)))
    (ν := (volume : Measure (Fin e × Fin n → ℂ))) hg0.aemeasurable
      ((measurable_rowGauss h).indicator hA).aemeasurable
  rw [← Measure.volume_eq_prod] at hprod
  rw [← lintegral_map hF Ψ.continuous.measurable, hc, lintegral_smul_measure, hprod,
    lintegral_indicator hA]
  rw [ENNReal.smul_def, smul_eq_mul, mul_assoc]

theorem main (h : HermNorm n) (G : (Fin e × Fin n → ℂ) → ℝ)
    (hfin : gaussM (e + 1) n Set.univ < ⊤)
    (hG : IntegrableOn (fun u => G (nrmGroups h e u)) (ballProd h e)) :
    Integrable (fun π : Fin (e + 1) → Fin n → ℂ => G (nrmGroups h e (coefRows h π)))
        (gaussM (e + 1) n) ∧
      ∫ π, G (nrmGroups h e (coefRows h π)) ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * sphereMean h e G := by
  haveI : IsFiniteMeasure (gaussM (e + 1) n) := ⟨hfin⟩
  haveI : IsFiniteMeasure (volume.restrict (ballProd h e)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_ballProd_lt_top h e⟩
  obtain ⟨a, ha⟩ := map_coefRows (e := e) h
  have hmap : (gaussM (e + 1) n).map (coefRows h) =
      ((a • (exP e).withDensity (wt h)).prod (volume.restrict (ballProd h e))).map scT := by
    rw [ha, layer h, Measure.prod_smul_left, Measure.map_smul]
  have hac : a • (exP e).withDensity (wt h) ≪ exP e :=
    Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  refine transfer (gaussM (e + 1) n) (a • (exP e).withDensity (wt h))
    (volume.restrict (ballProd h e)) ?_ (measurable_coefRows h) measurable_scT hmap
    (F := fun u => G (nrmGroups h e u)) ?_ ?_ hG
  · rw [Measure.restrict_apply_univ]; exact (volume_ballProd_pos h e).ne'
  · rw [ha]
    exact (aesm h G hG.aestronglyMeasurable).mono_ac
      (Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _))
  · filter_upwards [hac.ae_le ae_pos_piExponential] with s hs u
    simp only [scT]
    rw [nrm_sc h (fun i => Real.sqrt_pos.2 (hs i)) u]

end

end ModelDimension.GSph
