import Mathlib
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import GroundTheory.AutomorphicForms.ReductionIwasawa
import GroundTheory.AutomorphicForms.NormDetDiagUnitsPosRealToUnits
import GroundTheory.AutomorphicForms.ReductionMeasure

namespace GroundTheory.Automorphic.Adele2

open NumberField IsDedekindDomain MeasureTheory Measure Matrix GroundTheory.Global
  GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing ENNReal

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def adeleMeasure2 : Measure (Fin 2 → 𝔸[K]) := Measure.pi fun _ => adeleMeasure K

instance : (adeleMeasure2 K).IsAddHaarMeasure := by
  unfold adeleMeasure2; infer_instance

instance : SigmaFinite (adeleMeasure2 K) := by
  unfold adeleMeasure2; infer_instance

variable {K}

def vecMulHomeomorph (g : GL (Fin 2) 𝔸[K]) : (Fin 2 → 𝔸[K]) ≃ₜ (Fin 2 → 𝔸[K]) where
  toFun x := x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K])
  invFun x := x ᵥ* ((g⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])
  left_inv x := by
    simp only
    rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  right_inv x := by
    simp only
    rw [vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
  continuous_toFun := continuous_id.matrix_vecMul continuous_const
  continuous_invFun := continuous_id.matrix_vecMul continuous_const

theorem measurable_vecMul (g : GL (Fin 2) 𝔸[K]) :
    Measurable fun x : Fin 2 → 𝔸[K] => x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K]) :=
  (vecMulHomeomorph g).continuous.measurable

theorem measurableEmbedding_vecMul (g : GL (Fin 2) 𝔸[K]) :
    MeasurableEmbedding fun x : Fin 2 → 𝔸[K] => x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K]) :=
  (vecMulHomeomorph g).toMeasurableEquiv.measurableEmbedding

def vecMulAddHom (g : GL (Fin 2) 𝔸[K]) : (Fin 2 → 𝔸[K]) →+ (Fin 2 → 𝔸[K]) :=
  AddMonoidHom.mk' (fun x => x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K])) fun x y => by rw [add_vecMul]

theorem isAddHaarMeasure_map_vecMul (g : GL (Fin 2) 𝔸[K]) :
    ((adeleMeasure2 K).map fun x => x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K])).IsAddHaarMeasure :=
  isAddHaarMeasure_map (adeleMeasure2 K) (vecMulAddHom g) (vecMulHomeomorph g).continuous
    (vecMulHomeomorph g).surjective (vecMulHomeomorph g).isClosedEmbedding.tendsto_cocompact

def unitBall2 : Set (Fin 2 → 𝔸[K]) :=
  {x | (∀ w : InfinitePlace K, euclidNorm (infComp w x) ≤ 1) ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ‖finComp v x‖ ≤ 1}

theorem forall_norm_finComp_le_one_iff (x : Fin 2 → 𝔸[K]) :
    (∀ v : HeightOneSpectrum (𝓞 K), ‖finComp v x‖ ≤ 1) ↔
      ∀ i, (x i).2 ∈ integralFiniteAdeles (𝓞 K) K := by
  simp only [mem_integralFiniteAdeles]
  constructor
  · intro h i v
    have hv := (pi_norm_le_iff_of_nonneg zero_le_one).1 (h v) i
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).2
      ((Valued.toNormedField.norm_le_one_iff).1 hv)
  · intro h v
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    exact norm_le_one_of_mem v (h i v)

theorem unitBall2_eq :
    (unitBall2 : Set (Fin 2 → 𝔸[K])) =
      {x | (∀ w : InfinitePlace K, euclidNorm (infComp w x) ≤ 1) ∧
        ∀ i, (x i).2 ∈ integralFiniteAdeles (𝓞 K) K} := by
  ext x
  simp only [unitBall2, Set.mem_ofPred_eq, forall_norm_finComp_le_one_iff]

theorem continuous_infComp (w : InfinitePlace K) :
    Continuous fun x : Fin 2 → 𝔸[K] => infComp w x :=
  continuous_pi fun i => (continuous_apply w).comp (continuous_fst.comp (continuous_apply i))

theorem isClosed_unitBall2 : IsClosed (unitBall2 : Set (Fin 2 → 𝔸[K])) := by
  rw [unitBall2_eq, Set.ofPred_and]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun w =>
      isClosed_le (continuous_euclidNorm.comp (continuous_infComp w)) continuous_const
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i =>
      ((isCompact_integralFiniteAdeles K).isClosed).preimage
        (continuous_snd.comp (continuous_apply i))

theorem isCompact_unitBall2 : IsCompact (unitBall2 : Set (Fin 2 → 𝔸[K])) := by
  set C : Set 𝔸[K] := {a | (∀ w, ‖a.1 w‖ ≤ 1) ∧ a.2 ∈ integralFiniteAdeles (𝓞 K) K}
  have hC : IsCompact C := by
    have hB : IsCompact (Set.univ.pi fun w : InfinitePlace K =>
        Metric.closedBall (0 : w.Completion) 1) :=
      isCompact_univ_pi fun w => isCompact_closedBall 0 1
    have h := hB.prod (isCompact_integralFiniteAdeles K)
    have hCeq : C = (Set.univ.pi fun w : InfinitePlace K =>
        Metric.closedBall (0 : w.Completion) 1) ×ˢ
          (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
      ext a
      change _ ↔ (a.1 ∈ Set.univ.pi (fun w : InfinitePlace K =>
        Metric.closedBall (0 : w.Completion) 1) ∧ a.2 ∈ (integralFiniteAdeles (𝓞 K) K : Set _))
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun w _ => mem_closedBall_zero_iff.mpr (h1 w), h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun w => mem_closedBall_zero_iff.mp (h1 w (Set.mem_univ w)), h2⟩
    rw [hCeq]
    exact h
  refine (isCompact_univ_pi fun _ : Fin 2 => hC).of_isClosed_subset isClosed_unitBall2 ?_
  intro x hx i _
  rw [unitBall2_eq] at hx
  refine ⟨fun w => ?_, hx.2 i⟩
  exact (norm_le_euclidNorm (infComp w x) i).trans (hx.1 w)

theorem measurableSet_unitBall2 : MeasurableSet (unitBall2 : Set (Fin 2 → 𝔸[K])) :=
  isClosed_unitBall2.measurableSet

theorem adeleMeasure2_unitBall2_ne_top : adeleMeasure2 K unitBall2 ≠ ⊤ :=
  isCompact_unitBall2.measure_lt_top.ne

theorem adeleMeasure2_unitBall2_ne_zero : adeleMeasure2 K unitBall2 ≠ 0 := by
  set U : Set (Fin 2 → 𝔸[K]) :=
    {x | (∀ i, ∀ w : InfinitePlace K, ‖(x i).1 w‖ < 1 / 2) ∧
      ∀ i, (x i).2 ∈ integralFiniteAdeles (𝓞 K) K}
  have hU : IsOpen U := by
    simp only [U]
    rw [Set.ofPred_and]
    refine IsOpen.inter ?_ ?_
    · simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun w =>
        isOpen_lt (continuous_norm.comp ((continuous_apply w).comp
          (continuous_fst.comp (continuous_apply i)))) continuous_const
    · simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i =>
        isOpen_integralFiniteAdeles.preimage (continuous_snd.comp (continuous_apply i))
  have h0 : (0 : Fin 2 → 𝔸[K]) ∈ U :=
    ⟨fun i w => by
      have h0 : ((0 : Fin 2 → 𝔸[K]) i).1 w = 0 := rfl
      rw [h0, norm_zero]
      norm_num, fun i => zero_mem _⟩
  have hsub : U ⊆ unitBall2 := by
    intro x hx
    rw [unitBall2_eq]
    refine ⟨fun w => ?_, hx.2⟩
    rw [euclidNorm]
    refine Real.sqrt_le_one.mpr ?_
    have hle : ∀ i, ‖infComp w x i‖ ^ 2 ≤ (1 / 2) ^ 2 := fun i =>
      pow_le_pow_left₀ (norm_nonneg _) (hx.1 i w).le 2
    calc ∑ i, ‖infComp w x i‖ ^ 2 ≤ ∑ _i : Fin 2, ((1 : ℝ) / 2) ^ 2 :=
          Finset.sum_le_sum fun i _ => hle i
      _ ≤ 1 := by norm_num
  exact (pos_iff_ne_zero.mp ((hU.measure_pos (adeleMeasure2 K) ⟨0, h0⟩).trans_le
    (measure_mono hsub)))

theorem vecMul_mem_unitBall2_iff {k : GL (Fin 2) 𝔸[K]}
    (hk : k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2))) (x : Fin 2 → 𝔸[K]) :
    x ᵥ* (k : Matrix (Fin 2) (Fin 2) 𝔸[K]) ∈ unitBall2 ↔ x ∈ unitBall2 := by
  simp only [unitBall2, Set.mem_ofPred_eq]
  have h1 : ∀ w : InfinitePlace K,
      euclidNorm (infComp w (x ᵥ* (k : Matrix (Fin 2) (Fin 2) 𝔸[K]))) =
        euclidNorm (infComp w x) :=
    fun w => by rw [infComp_vecMul_GL, hk.1 w]
  have h2 : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖finComp v (x ᵥ* (k : Matrix (Fin 2) (Fin 2) 𝔸[K]))‖ = ‖finComp v x‖ :=
    fun v => by rw [finComp_vecMul_GL, norm_vecMul_integralGL v (hk.2 v)]
  simp only [h1, h2]

theorem map_vecMul_maxCompact {k : GL (Fin 2) 𝔸[K]}
    (hk : k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2))) :
    (adeleMeasure2 K).map (fun x => x ᵥ* (k : Matrix (Fin 2) (Fin 2) 𝔸[K])) = adeleMeasure2 K := by
  set ν := (adeleMeasure2 K).map fun x => x ᵥ* (k : Matrix (Fin 2) (Fin 2) 𝔸[K])
  have : ν.IsAddHaarMeasure := isAddHaarMeasure_map_vecMul k
  have h := isAddLeftInvariant_eq_smul ν (adeleMeasure2 K)
  set c := ν.addHaarScalarFactor (adeleMeasure2 K)
  have hS : ν unitBall2 = adeleMeasure2 K unitBall2 := by
    rw [map_apply (measurable_vecMul k) measurableSet_unitBall2]
    congr 1
    ext x
    exact vecMul_mem_unitBall2_iff hk x
  have hc : (c : ℝ≥0∞) = 1 := by
    rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hS
    have h1 : (c : ℝ≥0∞) * adeleMeasure2 K unitBall2 = 1 * adeleMeasure2 K unitBall2 := by
      rw [one_mul]; exact hS
    exact (ENNReal.mul_left_inj adeleMeasure2_unitBall2_ne_zero adeleMeasure2_unitBall2_ne_top).1 h1
  rw [h]
  rw [show c = 1 from by exact_mod_cast hc, one_smul]

theorem ideleModule_det_of_mem_maxCompact {k : GL (Fin 2) 𝔸[K]}
    (hk : k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2))) :
    IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det k) = 1 :=
  eq_one_of_isCompact isCompact_maxCompact ((IdeleGroup.ideleModule K).comp (AdelicGLn.det K 2))
    (continuous_subtype_val.comp
      (IdeleGroup.continuous_ideleModule.comp (AdelicGLn.continuous_det K 2))) hk

theorem measurePreserving_shear (t : 𝔸[K]) :
    MeasurePreserving (fun p : 𝔸[K] × 𝔸[K] => (p.1, p.1 * t + p.2))
      ((adeleMeasure K).prod (adeleMeasure K)) ((adeleMeasure K).prod (adeleMeasure K)) := by
  have hc : Continuous fun p : 𝔸[K] × 𝔸[K] => p.1 * t + p.2 :=
    (continuous_fst.mul continuous_const).add continuous_snd
  exact MeasurePreserving.skew_product (μa := adeleMeasure K) (μb := adeleMeasure K)
    (μc := adeleMeasure K) (μd := adeleMeasure K) (f := id) (g := fun a b => a * t + b)
    (MeasurePreserving.id _) hc.measurable
    (Filter.Eventually.of_forall fun a => map_add_left_eq_self (adeleMeasure K) (a * t))

theorem map_vecMul_adelicBorel {b : GL (Fin 2) 𝔸[K]}
    (hb : b ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL K 2))) :
    (adeleMeasure2 K).map (fun x => x ᵥ* (b : Matrix (Fin 2) (Fin 2) 𝔸[K])) =
      ENNReal.ofReal ((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ))⁻¹ •
        adeleMeasure2 K := by
  set M : Matrix (Fin 2) (Fin 2) 𝔸[K] := ↑b
  have h10 : M 1 0 = 0 := hb (show (0 : Fin 2) < 1 by decide)
  set A : IdeleGroup K := (isUnit_apply_self_of_mem_adelicBorel hb 0).unit
  set D : IdeleGroup K := (isUnit_apply_self_of_mem_adelicBorel hb 1).unit
  have hA : (A : 𝔸[K]) = M 0 0 := IsUnit.unit_spec _
  have hD : (D : 𝔸[K]) = M 1 1 := IsUnit.unit_spec _
  have hdet : Matrix.GeneralLinearGroup.det b = A * D := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, hA, hD]
    show M.det = _
    rw [det_fin_two, h10, mul_zero, sub_zero]
  set t : 𝔸[K] := ((A⁻¹ : IdeleGroup K) : 𝔸[K]) * M 0 1
  set e := (MeasurableEquiv.finTwoArrow : (Fin 2 → 𝔸[K]) ≃ᵐ 𝔸[K] × 𝔸[K])
  have he : MeasurePreserving e (adeleMeasure2 K) ((adeleMeasure K).prod (adeleMeasure K)) :=
    measurePreserving_finTwoArrow (adeleMeasure K)
  set diag : 𝔸[K] × 𝔸[K] → 𝔸[K] × 𝔸[K] := Prod.map (fun y => A • y) (fun y => D • y)
  set shear : 𝔸[K] × 𝔸[K] → 𝔸[K] × 𝔸[K] := fun p => (p.1, p.1 * t + p.2)
  have hfun : (fun x : Fin 2 → 𝔸[K] => x ᵥ* M) = e.symm ∘ shear ∘ diag ∘ e := by
    funext x
    have hAA : M 0 0 * ((A⁻¹ : IdeleGroup K) : 𝔸[K]) = 1 := by
      rw [← hA, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    ext j
    fin_cases j
    · simp [e, diag, shear, vecMul, dotProduct, Fin.sum_univ_two, h10, Units.smul_def, hA,
        MeasurableEquiv.finTwoArrow_symm_apply, MeasurableEquiv.finTwoArrow_apply]
      ring
    · simp [e, diag, shear, t, vecMul, dotProduct, Fin.sum_univ_two, Units.smul_def, hA, hD,
        MeasurableEquiv.finTwoArrow_symm_apply, MeasurableEquiv.finTwoArrow_apply]
      linear_combination (-(x 0 * M 0 1)) * hAA
  have hsm : ∀ a : IdeleGroup K, Measurable fun y : 𝔸[K] => a • y := fun a =>
    (Homeomorph.smul a).continuous.measurable
  have hdiag : Measurable diag := (hsm A).prodMap (hsm D)
  have hshear : Measurable shear := (measurePreserving_shear t).measurable
  have hmapdiag : ((adeleMeasure K).prod (adeleMeasure K)).map diag =
      (ENNReal.ofReal ((IdeleGroup.ideleModule K A : ℝ))⁻¹ *
        ENNReal.ofReal ((IdeleGroup.ideleModule K D : ℝ))⁻¹) •
        (adeleMeasure K).prod (adeleMeasure K) := by
    rw [← map_prod_map _ _ (hsm A) (hsm D), map_smul_adeleMeasure, map_smul_adeleMeasure,
      prod_smul_left, prod_smul_right, smul_smul]
  have hconst : ENNReal.ofReal ((IdeleGroup.ideleModule K A : ℝ))⁻¹ *
      ENNReal.ofReal ((IdeleGroup.ideleModule K D : ℝ))⁻¹ =
      ENNReal.ofReal ((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ))⁻¹ := by
    rw [hdet, map_mul, ← ENNReal.ofReal_mul (inv_nonneg.2 (IdeleGroup.ideleModule K A).2.le),
      ← mul_inv]
    rfl
  rw [hfun, ← map_map e.symm.measurable (hshear.comp (hdiag.comp e.measurable)),
    ← map_map hshear (hdiag.comp e.measurable), ← map_map hdiag e.measurable, he.map_eq,
    hmapdiag, Measure.map_smul, (measurePreserving_shear t).map_eq, Measure.map_smul,
    he.symm.map_eq, hconst]

theorem map_vecMul_adeleMeasure2 (g : GL (Fin 2) 𝔸[K]) :
    (adeleMeasure2 K).map (fun x => x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K])) =
      ENNReal.ofReal ((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det g) : ℝ))⁻¹ •
        adeleMeasure2 K := by
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_adelicBorel_mul_maxCompact (K := K) (n := 2) g
  have hcomp : (fun x : Fin 2 → 𝔸[K] =>
      x ᵥ* ((b * k : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])) =
      (fun x => x ᵥ* (k : Matrix (Fin 2) (Fin 2) 𝔸[K])) ∘
        (fun x => x ᵥ* (b : Matrix (Fin 2) (Fin 2) 𝔸[K])) := by
    funext x
    simp only [Function.comp_apply, Units.val_mul, vecMul_vecMul]
  rw [hcomp, ← map_map (measurable_vecMul k) (measurable_vecMul b), map_vecMul_adelicBorel hb,
    Measure.map_smul, map_vecMul_maxCompact hk, map_mul, map_mul,
    ideleModule_det_of_mem_maxCompact hk, mul_one]

theorem integral_comp_vecMul (g : GL (Fin 2) 𝔸[K]) (f : (Fin 2 → 𝔸[K]) → ℂ) :
    ∫ x, f (x ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K])) ∂adeleMeasure2 K =
      (((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det g) : ℝ))⁻¹ : ℂ) *
        ∫ x, f x ∂adeleMeasure2 K := by
  rw [← (measurableEmbedding_vecMul g).integral_map, map_vecMul_adeleMeasure2,
    integral_smul_measure, ENNReal.toReal_ofReal
      (inv_nonneg.2 (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det g)).2.le),
    Complex.real_smul, Complex.ofReal_inv]

end

end GroundTheory.Automorphic.Adele2
