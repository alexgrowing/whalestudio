import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyIntegral
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyChern
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ContDiff
open MeasureTheory Topology Set MvPolynomial

noncomputable section

variable {N : ℕ}

namespace CP

instance instMeasurableSpace : MeasurableSpace (CP N) := borel (CP N)

instance instBorelSpace : BorelSpace (CP N) := ⟨rfl⟩

def fsChartMeasure (i : Fin (N + 1)) : Measure (Fin N → ℂ) :=
  volume.withDensity fun z => ENNReal.ofReal (fsVolumeDensity i z)

def fsMeasure (N : ℕ) : Measure (CP N) := (fsChartMeasure (N := N) 0).map (chartInv 0)

lemma measurable_chartInv (i : Fin (N + 1)) : Measurable (chartInv (N := N) i) :=
  (continuous_chartInv i).measurable

lemma measurable_fsVolumeDensity (i : Fin (N + 1)) :
    Measurable (fsVolumeDensity (N := N) i) := by
  have : fsVolumeDensity (N := N) i = fun z =>
      N.factorial / (Real.pi ^ N * (1 + normSqSum z) ^ (N + 1)) := by
    funext z; exact fsVolumeDensity_eq i z
  rw [this]
  unfold normSqSum
  fun_prop

theorem lintegral_fsVolumeDensity (i : Fin (N + 1)) :
    ∫⁻ z, ENNReal.ofReal (fsVolumeDensity i z) = 1 := by
  have h := lintegral_pi_complex_monomial 0 N (fun _ => 0) 1 one_pos
  simp only [mul_zero, pow_zero, Finset.prod_const_one, Finset.sum_const_zero, zero_add,
    add_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_pow, div_one] at h
  have hpt : ∀ z : Fin N → ℂ, ENNReal.ofReal (fsVolumeDensity i z) =
      ENNReal.ofReal (N.factorial / Real.pi ^ N) *
        ENNReal.ofReal (1 / (1 + ∑ j, ‖z j‖ ^ 2) ^ (N + 1)) := by
    intro z
    rw [← ENNReal.ofReal_mul (by positivity), fsVolumeDensity_eq]
    congr 1
    rw [normSqSum]
    field_simp
  rw [lintegral_congr hpt, lintegral_const_mul _ (by fun_prop), h, ← ENNReal.ofReal_mul (by positivity)]
  have hpi := Real.pi_pos
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  rw [show (N.factorial : ℝ) / Real.pi ^ N * (Real.pi ^ N / N.factorial) = 1 by field_simp]
  simp

theorem integral_fsVolumeDensity (i : Fin (N + 1)) : ∫ z, fsVolumeDensity i z = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => (fsVolumeDensity_pos i z).le)
    (measurable_fsVolumeDensity i).aestronglyMeasurable, lintegral_fsVolumeDensity]
  simp

theorem fsMeasure_univ : fsMeasure N univ = 1 := by
  rw [fsMeasure, Measure.map_apply (measurable_chartInv 0) MeasurableSet.univ, preimage_univ,
    fsChartMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_fsVolumeDensity]

instance (N : ℕ) : IsProbabilityMeasure (fsMeasure N) := ⟨fsMeasure_univ⟩

theorem fsMeasure_compl_chartDomain : fsMeasure N (chartDomain 0)ᶜ = 0 := by
  rw [fsMeasure, Measure.map_apply (measurable_chartInv 0)
    ((isOpen_chartDomain 0).measurableSet.compl)]
  have : chartInv (N := N) 0 ⁻¹' (chartDomain 0)ᶜ = ∅ := by
    ext z; simp [chartInv_mem]
  rw [this, measure_empty]

abbrev H0 (N n : ℕ) : Submodule ℂ (MvPolynomial (Fin (N + 1)) ℂ) :=
  homogeneousSubmodule (Fin (N + 1)) ℂ n

def fsNormPoly (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (x : CP N) : ℝ :=
  ‖eval x.rep P‖ / norm2 x.rep ^ n

theorem fsNormPoly_mk {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n)
    (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    fsNormPoly n P (Projectivization.mk ℂ v hv) = ‖eval v P‖ / norm2 v ^ n := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [fsNormPoly, ← ha, Units.smul_def]
  have he : eval ((a : ℂ) • v) P = (a : ℂ) ^ n * eval v P :=
    evalAt_smul (RingHom.id ℂ) hP (a : ℂ) v
  have hn : 0 < norm2 v := euclideanNorm_pos hv
  have ha0 : 0 < ‖(a : ℂ)‖ := norm_pos_iff.mpr a.ne_zero
  rw [he, norm_mul, norm_pow, euclideanNorm_smul, mul_pow]
  field_simp

def linearPoly (ℓ : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ) : MvPolynomial (Fin (N + 1)) ℂ :=
  ∑ i, C (ℓ (Pi.single i 1)) * X i

lemma eval_linearPoly (ℓ : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ) (v : Fin (N + 1) → ℂ) :
    eval v (linearPoly ℓ) = ℓ v := by
  rw [linearPoly, map_sum, LinearMap.pi_apply_eq_sum_univ ℓ v]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, eval_C, eval_X, smul_eq_mul]
  rw [mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

lemma linearPoly_mem_sections_degree_one (ℓ : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ) : linearPoly ℓ ∈ H0 N 1 := by
  rw [mem_homogeneousSubmodule, linearPoly]
  exact IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_C _ _).mul (isHomogeneous_X _ i)

theorem fsNormPoly_linearPoly (ℓ : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ) (x : CP N) :
    fsNormPoly 1 (linearPoly ℓ) x = fsNorm x (restrictForm ℓ x) := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [fsNormPoly_mk ((mem_homogeneousSubmodule _ _).mp (linearPoly_mem_sections_degree_one ℓ)) v hv,
      fsNorm_restrictForm_mk, eval_linearPoly, pow_one]

lemma fsNormPoly_nonneg (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (x : CP N) :
    0 ≤ fsNormPoly n P x :=
  div_nonneg (norm_nonneg _) (pow_nonneg (euclideanNorm_pos x.rep_nonzero).le _)

theorem continuous_fsNormPoly {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n) :
    Continuous (fsNormPoly (N := N) n P) := by
  rw [ProjTopology.continuous_iff]
  have : fsNormPoly (N := N) n P ∘ Projectivization.mk' ℂ =
      fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => ‖eval v.1 P‖ / norm2 v.1 ^ n := by
    funext ⟨v, hv⟩; exact fsNormPoly_mk hP v hv
  rw [this]
  have hc : Continuous fun v : Fin (N + 1) → ℂ => norm2 v :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
      (continuous_norm.comp (continuous_apply j)).pow 2)
  refine Continuous.div ?_ ((hc.comp continuous_subtype_val).pow n)
    fun v => (pow_pos (euclideanNorm_pos v.2) n).ne'
  exact continuous_norm.comp ((MvPolynomial.continuous_eval P).comp continuous_subtype_val)

theorem fsNormPoly_le {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n)
    (x : CP N) : fsNormPoly n P x ≤ ∑ d ∈ P.support, ‖P.coeff d‖ := by
  have hn : 0 < norm2 x.rep := euclideanNorm_pos x.rep_nonzero
  rw [fsNormPoly, div_le_iff₀ (pow_pos hn n), eval_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hdeg : ∑ i, d i = n := by
    have := hP.degree_eq_sum_deg_support hd
    rw [this]
    exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by simpa using hi).symm
  calc ∏ i, ‖x.rep i ^ d i‖ ≤ ∏ i, norm2 x.rep ^ d i := by
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_norm2 _ i) _
    _ = norm2 x.rep ^ n := by rw [Finset.prod_pow_eq_pow_sum, hdeg]

def supNorm (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) : ℝ := ⨆ x : CP N, fsNormPoly n P x

lemma bddAbove_fsNormPoly {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n) :
    BddAbove (range (fsNormPoly (N := N) n P)) :=
  ⟨_, forall_mem_range.mpr (fsNormPoly_le hP)⟩

theorem fsNormPoly_le_supNorm {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n)
    (x : CP N) : fsNormPoly n P x ≤ supNorm n P :=
  le_ciSup (bddAbove_fsNormPoly hP) x

theorem exists_supNorm_eq {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n) :
    ∃ x : CP N, fsNormPoly n P x = supNorm n P := by
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty (α := CP N))
    (continuous_fsNormPoly (N := N) hP).continuousOn
  refine ⟨x, le_antisymm (fsNormPoly_le_supNorm hP x) (ciSup_le fun y => hx (mem_univ y))⟩

theorem eq_zero_of_fsNormPoly {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n)
    (h : ∀ x : CP N, fsNormPoly n P x = 0) : P = 0 := by
  have hv : ∀ v : Fin (N + 1) → ℂ, v ≠ 0 → eval v P = 0 := by
    intro v hv
    have := h (Projectivization.mk ℂ v hv)
    rw [fsNormPoly_mk hP v hv, div_eq_zero_iff, norm_eq_zero] at this
    exact this.resolve_right (pow_pos (euclideanNorm_pos hv) n).ne'
  apply MvPolynomial.funext
  intro v
  rw [map_zero]
  by_cases h0 : v = 0
  · subst h0
    have hw : (Pi.single 0 1 : Fin (N + 1) → ℂ) ≠ 0 := by simp
    have h1 : eval ((0 : ℂ) • (Pi.single 0 1 : Fin (N + 1) → ℂ)) P =
        (0 : ℂ) ^ n * eval (Pi.single 0 1) P := evalAt_smul (RingHom.id ℂ) hP 0 _
    rw [zero_smul, hv _ hw, mul_zero] at h1
    exact h1
  · exact hv v h0

theorem supNorm_eq_zero_iff {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n) :
    supNorm (N := N) n P = 0 ↔ P = 0 := by
  constructor
  · intro h0
    refine eq_zero_of_fsNormPoly (N := N) hP fun x => le_antisymm ?_ (fsNormPoly_nonneg _ _ _)
    exact h0 ▸ fsNormPoly_le_supNorm hP x
  · rintro rfl
    simp [supNorm, fsNormPoly]

def sectionL2NormSq (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) : ℝ :=
  ∫ x, fsNormPoly n P x ^ 2 ∂fsMeasure N

def l2Norm (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) : ℝ := √(sectionL2NormSq (N := N) n P)

lemma sectionL2NormSq_nonneg (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) : 0 ≤ sectionL2NormSq (N := N) n P :=
  integral_nonneg fun _ => sq_nonneg _

lemma fubiniStudy_l2Norm_sq_eq (n : ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) :
    l2Norm (N := N) n P ^ 2 = sectionL2NormSq n P := Real.sq_sqrt (sectionL2NormSq_nonneg n P)

theorem fubiniStudy_l2Norm_le_supNorm {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n) :
    l2Norm (N := N) n P ≤ supNorm n P := by
  have hs : 0 ≤ supNorm (N := N) n P := (fsNormPoly_nonneg n P (Classical.arbitrary _)).trans
    (fsNormPoly_le_supNorm hP _)
  rw [l2Norm, Real.sqrt_le_left hs]
  have hb : ∀ x : CP N, fsNormPoly n P x ^ 2 ≤ supNorm n P ^ 2 := fun x =>
    pow_le_pow_left₀ (fsNormPoly_nonneg _ _ _) (fsNormPoly_le_supNorm hP x) 2
  calc sectionL2NormSq n P ≤ ∫ _ : CP N, supNorm n P ^ 2 ∂fsMeasure N := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall hb)
    _ = supNorm n P ^ 2 := by simp

lemma chartVec_zero_succ (z : Fin N → ℂ) (j : Fin N) : chartVec 0 z j.succ = z j := by
  rw [← Fin.succAbove_zero, chartVec_succAbove]

lemma fsNormPoly_monomial_sq_chartInv (a : Fin (N + 1) →₀ ℕ) (z : Fin N → ℂ) :
    fsNormPoly a.degree (monomial a (1 : ℂ)) (chartInv 0 z) ^ 2 =
      (∏ j, ‖z j‖ ^ (2 * a j.succ)) / (1 + ∑ j, ‖z j‖ ^ 2) ^ a.degree := by
  rw [chartInv, fsNormPoly_mk (isHomogeneous_monomial 1 rfl), eval_monomial, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), div_pow,
    show (norm2 (chartVec 0 z) ^ a.degree) ^ 2 = (norm2 (chartVec 0 z) ^ 2) ^ a.degree by ring,
    euclideanNorm_sq, normSq2_chartVec, norm_prod, Fin.prod_univ_succ, chartVec_self]
  simp only [one_pow, norm_one, one_mul, norm_pow, chartVec_zero_succ]
  congr 1
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm]

theorem fubiniStudy_l2Norm_monomial_sq (a : Fin (N + 1) →₀ ℕ) :
    l2Norm (N := N) a.degree (monomial a (1 : ℂ)) ^ 2 =
      (∏ i, ((a i).factorial : ℝ)) * N.factorial / (a.degree + N).factorial := by
  have hdeg : a.degree = a 0 + ∑ j : Fin N, a j.succ := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  have hfm : AEStronglyMeasurable (fun x : CP N => fsNormPoly a.degree (monomial a (1 : ℂ)) x ^ 2)
      (Measure.map (chartInv 0) (fsChartMeasure (N := N) 0)) :=
    ((continuous_fsNormPoly (isHomogeneous_monomial (1 : ℂ) rfl)).pow 2).aestronglyMeasurable
  rw [fubiniStudy_l2Norm_sq_eq, sectionL2NormSq, fsMeasure, integral_map (measurable_chartInv 0).aemeasurable hfm,
    fsChartMeasure]
  have hd : (fun z => ENNReal.ofReal (fsVolumeDensity (N := N) 0 z)) =
      fun z => (((fsVolumeDensity (N := N) 0 z).toNNReal : NNReal) : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul (measurable_fsVolumeDensity 0).real_toNNReal]
  have hpt : ∀ z : Fin N → ℂ, (fsVolumeDensity (N := N) 0 z).toNNReal •
      fsNormPoly a.degree (monomial a (1 : ℂ)) (chartInv 0 z) ^ 2 =
      (N.factorial / Real.pi ^ N) * ((∏ j, ‖z j‖ ^ (2 * a j.succ)) /
        (1 + ∑ j, ‖z j‖ ^ 2) ^ (∑ j : Fin N, a j.succ + N + 1 + a 0)) := by
    intro z
    rw [NNReal.smul_def, Real.coe_toNNReal _ (fsVolumeDensity_pos 0 z).le, smul_eq_mul,
      fsNormPoly_monomial_sq_chartInv, fsVolumeDensity_eq, normSqSum,
      show ∑ j : Fin N, a j.succ + N + 1 + a 0 = a.degree + (N + 1) by rw [hdeg]; ring, pow_add]
    have hS : 0 < 1 + ∑ j, ‖z j‖ ^ 2 := by positivity
    have hpi := Real.pi_pos
    field_simp
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    (integral_pi_complex_monomial (a 0) N (fun j => a j.succ) 1 one_pos).2,
    Fin.prod_univ_succ, show ∑ j : Fin N, a j.succ + N + a 0 = a.degree + N by rw [hdeg]; ring]
  have hpi := Real.pi_pos
  have hf : ((a.degree + N).factorial : ℝ) ≠ 0 := by positivity
  simp only [one_pow, div_one]
  field_simp

def x0 : H0 1 1 := ⟨X 0, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X ℂ 0)⟩

theorem fubiniStudyNorm_coordinate_chart (z : Fin 1 → ℂ) :
    fsNormPoly 1 (x0 : MvPolynomial (Fin 2) ℂ) (chartInv 0 z) = 1 / √(1 + ‖z 0‖ ^ 2) := by
  rw [x0, chartInv, fsNormPoly_mk (isHomogeneous_X ℂ 0), eval_X, chartVec_self, norm2,
    normSq2_chartVec]
  simp

theorem fubiniStudy_l2Norm_coordinate_sq : l2Norm (N := 1) 1 (x0 : MvPolynomial (Fin 2) ℂ) ^ 2 = 1 / 2 := by
  have h := fubiniStudy_l2Norm_monomial_sq (N := 1) (Finsupp.single 0 1)
  have hdeg : (Finsupp.single (0 : Fin 2) 1).degree = 1 := by simp
  have hX : (monomial (Finsupp.single (0 : Fin 2) 1) (1 : ℂ)) = X 0 := rfl
  rw [hdeg, hX] at h
  rw [x0, h]
  simp [Fin.prod_univ_two]

theorem chernCoeff_one (z : Fin 1 → ℂ) :
    chernCoeff (N := 1) 0 z 0 0 = ((1 / (2 * Real.pi * (1 + ‖z 0‖ ^ 2) ^ 2) : ℝ) : ℂ) := by
  rw [chernCoeff_apply]
  simp only [normSqSum, Fin.sum_univ_one, Matrix.one_apply_eq, Complex.conj_mul']
  have hS : 0 < 1 + ‖z 0‖ ^ 2 := by positivity
  have hS' : (1 + (‖z 0‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hS.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

example : fsMeasure 1 univ = 1 := fsMeasure_univ

example : restrictForm (coordForm 0) (chartInv (N := 1) 0 0) ≠ 0 :=
  restrictForm_coordForm_ne_zero 0 (chartInv_mem 0 0)

end CP

end

end GroundTheory.Heights₂.Heights
