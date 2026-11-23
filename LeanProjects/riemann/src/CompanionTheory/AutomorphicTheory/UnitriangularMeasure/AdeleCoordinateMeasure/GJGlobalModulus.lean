import Mathlib
import GroundTheory.AutomorphicForms.GL2.IdeleModuleDetOfMemMaxCompact
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import GroundTheory.AutomorphicForms.ReductionIwasawa
import GroundTheory.AutomorphicForms.ReductionHeight

set_option maxSynthPendingDepth 1

namespace GroundTheory.Automorphic.GJGlobal.Modulus

open NumberField IsDedekindDomain MeasureTheory Measure Matrix GroundTheory.Global
  GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.GJMatrix
open scoped NumberField.AdeleRing ENNReal NNReal

noncomputable section

section Shear

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R]
  [BorelSpace R] [SecondCountableTopology R] (μ : Measure R) [μ.IsAddLeftInvariant] [SigmaFinite μ]

theorem measurePreserving_vecMul_unitriangular : ∀ {m : ℕ} (u : Matrix (Fin m) (Fin m) R),
    (∀ i j : Fin m, j < i → u i j = 0) → (∀ i, u i i = 1) →
    MeasurePreserving (fun x : Fin m → R => x ᵥ* u) (Measure.pi fun _ => μ)
      (Measure.pi fun _ => μ)
  | 0, u, _, _ => by
    have h : (fun x : Fin 0 → R => x ᵥ* u) = id := funext fun x => funext fun i => i.elim0
    rw [h]
    exact MeasurePreserving.id _
  | m + 1, u, hlow, hdiag => by
    set u' : Matrix (Fin m) (Fin m) R := u.submatrix Fin.castSucc Fin.castSucc with hu'
    have ih := measurePreserving_vecMul_unitriangular u'
      (fun i j hij => hlow _ _ (Fin.castSucc_lt_castSucc_iff.2 hij)) (fun i => hdiag _)
    set f : (Fin m → R) → R := fun y => ∑ i, y i * u (Fin.castSucc i) (Fin.last m) with hf
    have hfc : Continuous f := continuous_finsetSum _ fun i _ =>
      (continuous_apply i).mul continuous_const
    set S : (Fin m → R) × R → (Fin m → R) × R := fun p => (p.1 ᵥ* u', f p.1 + p.2) with hS
    have hSmp : MeasurePreserving S ((Measure.pi fun _ => μ).prod μ)
        ((Measure.pi fun _ => μ).prod μ) :=
      ih.skew_product (g := fun y a => f y + a)
        ((hfc.comp continuous_fst).add continuous_snd).measurable
        (Filter.Eventually.of_forall fun y => map_add_left_eq_self μ (f y))
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => R) (Fin.last m)
    have he : MeasurePreserving e (Measure.pi fun _ => μ)
        (μ.prod (Measure.pi fun _ : Fin m => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) (Fin.last m)
    have key : ∀ x : Fin (m + 1) → R, e (x ᵥ* u) = Prod.swap (S (Prod.swap (e x))) := by
      intro x
      have e1 : ∀ z : Fin (m + 1) → R, e z = (z (Fin.last m), fun j => z (Fin.castSucc j)) := by
        intro z
        simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
        rfl
      rw [e1, e1]
      simp only [hS, Prod.swap_prod_mk, Prod.mk.injEq]
      constructor
      · rw [vecMul, dotProduct, Fin.sum_univ_castSucc, hdiag, mul_one, add_comm]
      · funext j
        rw [vecMul, dotProduct, Fin.sum_univ_castSucc, hlow _ _ (Fin.castSucc_lt_last j),
          mul_zero, add_zero]
        rfl
    have hfun : (fun x : Fin (m + 1) → R => x ᵥ* u) =
        e.symm ∘ (Prod.swap ∘ S ∘ Prod.swap ∘ e) := by
      funext x
      simp only [Function.comp_apply]
      rw [← key, MeasurableEquiv.symm_apply_apply]
    rw [hfun]
    exact he.symm.comp (measurePreserving_swap.comp (hSmp.comp (measurePreserving_swap.comp he)))

end Shear

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def vecMulHomeomorph (g : GL (Fin n) 𝔸[K]) : (Fin n → 𝔸[K]) ≃ₜ (Fin n → 𝔸[K]) where
  toFun x := x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])
  invFun x := x ᵥ* ((g⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])
  left_inv x := by
    simp only
    rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  right_inv x := by
    simp only
    rw [vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
  continuous_toFun := continuous_id.matrix_vecMul continuous_const
  continuous_invFun := continuous_id.matrix_vecMul continuous_const

theorem measurable_vecMul' (g : GL (Fin n) 𝔸[K]) :
    Measurable fun x : Fin n → 𝔸[K] => x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]) :=
  (vecMulHomeomorph g).continuous.measurable

def vecMulAddHom' (g : GL (Fin n) 𝔸[K]) : (Fin n → 𝔸[K]) →+ (Fin n → 𝔸[K]) :=
  AddMonoidHom.mk' (fun x => x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) fun x y => by rw [add_vecMul]

theorem isAddHaarMeasure_map_vecMul' (g : GL (Fin n) 𝔸[K]) :
    ((adeleMeasurePi K (ι := Fin n)).map fun x => x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])).IsAddHaarMeasure :=
  isAddHaarMeasure_map (adeleMeasurePi K) (vecMulAddHom' g) (vecMulHomeomorph g).continuous
    (vecMulHomeomorph g).surjective (vecMulHomeomorph g).isClosedEmbedding.tendsto_cocompact

def unitBall : Set (Fin n → 𝔸[K]) :=
  {x | (∀ w : InfinitePlace K, euclidNorm (infComp w x) ≤ 1) ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ‖finComp v x‖ ≤ 1}

theorem forall_norm_finComp_le_one_iff' (x : Fin n → 𝔸[K]) :
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

theorem unitBall_eq :
    (unitBall : Set (Fin n → 𝔸[K])) =
      {x | (∀ w : InfinitePlace K, euclidNorm (infComp w x) ≤ 1) ∧
        ∀ i, (x i).2 ∈ integralFiniteAdeles (𝓞 K) K} := by
  ext x
  simp only [unitBall, Set.mem_ofPred_eq, forall_norm_finComp_le_one_iff']

theorem continuous_infComp' (w : InfinitePlace K) :
    Continuous fun x : Fin n → 𝔸[K] => infComp w x :=
  continuous_pi fun i => (continuous_apply w).comp (continuous_fst.comp (continuous_apply i))

theorem isClosed_unitBall : IsClosed (unitBall : Set (Fin n → 𝔸[K])) := by
  rw [unitBall_eq, Set.ofPred_and]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun w =>
      isClosed_le (continuous_euclidNorm.comp (continuous_infComp' w)) continuous_const
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i =>
      ((isCompact_integralFiniteAdeles K).isClosed).preimage
        (continuous_snd.comp (continuous_apply i))

theorem isCompact_unitBall : IsCompact (unitBall : Set (Fin n → 𝔸[K])) := by
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
  refine (isCompact_univ_pi fun _ : Fin n => hC).of_isClosed_subset isClosed_unitBall ?_
  intro x hx i _
  rw [unitBall_eq] at hx
  refine ⟨fun w => ?_, hx.2 i⟩
  exact (norm_le_euclidNorm (infComp w x) i).trans (hx.1 w)

theorem measurableSet_unitBall : MeasurableSet (unitBall : Set (Fin n → 𝔸[K])) :=
  isClosed_unitBall.measurableSet

theorem adeleMeasurePi_unitBall_ne_top : adeleMeasurePi K (unitBall : Set (Fin n → 𝔸[K])) ≠ ⊤ :=
  isCompact_unitBall.measure_lt_top.ne

theorem adeleMeasurePi_unitBall_ne_zero : adeleMeasurePi K (unitBall : Set (Fin n → 𝔸[K])) ≠ 0 := by
  set U : Set (Fin n → 𝔸[K]) :=
    {x | (∀ i, ∀ w : InfinitePlace K, ‖(x i).1 w‖ < 1 / ((n : ℝ) + 1)) ∧
      ∀ i, (x i).2 ∈ integralFiniteAdeles (𝓞 K) K}
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
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
  have h0 : (0 : Fin n → 𝔸[K]) ∈ U :=
    ⟨fun i w => by
      have h0 : ((0 : Fin n → 𝔸[K]) i).1 w = 0 := rfl
      rw [h0, norm_zero]
      positivity, fun i => zero_mem _⟩
  have hsub : U ⊆ unitBall := by
    intro x hx
    rw [unitBall_eq]
    refine ⟨fun w => ?_, hx.2⟩
    rw [euclidNorm]
    refine Real.sqrt_le_one.mpr ?_
    have hle : ∀ i, ‖infComp w x i‖ ^ 2 ≤ (1 / ((n : ℝ) + 1)) ^ 2 := fun i =>
      pow_le_pow_left₀ (norm_nonneg _) (hx.1 i w).le 2
    calc ∑ i, ‖infComp w x i‖ ^ 2 ≤ ∑ _i : Fin n, (1 / ((n : ℝ) + 1)) ^ 2 :=
          Finset.sum_le_sum fun i _ => hle i
      _ = (n : ℝ) * (1 / ((n : ℝ) + 1)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ 1 := by
          rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
          nlinarith
  exact (pos_iff_ne_zero.mp ((hU.measure_pos (adeleMeasurePi K) ⟨0, h0⟩).trans_le
    (measure_mono hsub)))

theorem vecMul_mem_unitBall_iff {k : GL (Fin n) 𝔸[K]}
    (hk : k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n))) (x : Fin n → 𝔸[K]) :
    x ᵥ* (k : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ unitBall ↔ x ∈ unitBall := by
  simp only [unitBall, Set.mem_ofPred_eq]
  have h1 : ∀ w : InfinitePlace K,
      euclidNorm (infComp w (x ᵥ* (k : Matrix (Fin n) (Fin n) 𝔸[K]))) =
        euclidNorm (infComp w x) :=
    fun w => by rw [infComp_vecMul_GL, hk.1 w]
  have h2 : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖finComp v (x ᵥ* (k : Matrix (Fin n) (Fin n) 𝔸[K]))‖ = ‖finComp v x‖ :=
    fun v => by rw [finComp_vecMul_GL, norm_vecMul_integralGL v (hk.2 v)]
  simp only [h1, h2]

theorem map_vecMul_maxCompact' {k : GL (Fin n) 𝔸[K]}
    (hk : k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n))) :
    (adeleMeasurePi K).map (fun x => x ᵥ* (k : Matrix (Fin n) (Fin n) 𝔸[K])) =
      adeleMeasurePi K (ι := Fin n) := by
  set ν := (adeleMeasurePi K (ι := Fin n)).map fun x => x ᵥ* (k : Matrix (Fin n) (Fin n) 𝔸[K])
  have : ν.IsAddHaarMeasure := isAddHaarMeasure_map_vecMul' k
  have h := isAddLeftInvariant_eq_smul ν (adeleMeasurePi K (ι := Fin n))
  set c := ν.addHaarScalarFactor (adeleMeasurePi K (ι := Fin n))
  have hS : ν (unitBall : Set (Fin n → 𝔸[K])) = adeleMeasurePi K (unitBall : Set (Fin n → 𝔸[K])) := by
    rw [map_apply (measurable_vecMul' k) measurableSet_unitBall]
    congr 1
    ext x
    exact vecMul_mem_unitBall_iff hk x
  have hc : (c : ℝ≥0∞) = 1 := by
    rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hS
    have h1 : (c : ℝ≥0∞) * adeleMeasurePi K (unitBall : Set (Fin n → 𝔸[K])) =
        1 * adeleMeasurePi K (unitBall : Set (Fin n → 𝔸[K])) := by
      rw [one_mul]; exact hS
    exact (ENNReal.mul_left_inj adeleMeasurePi_unitBall_ne_zero adeleMeasurePi_unitBall_ne_top).1 h1
  rw [h]
  rw [show c = 1 from by exact_mod_cast hc, one_smul]

theorem ideleModule_det_of_mem_maxCompact' {k : GL (Fin n) 𝔸[K]}
    (hk : k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n))) :
    IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det k) = 1 :=
  eq_one_of_isCompact isCompact_maxCompact ((IdeleGroup.ideleModule K).comp (AdelicGLn.det K n))
    (continuous_subtype_val.comp
      (IdeleGroup.continuous_ideleModule.comp (AdelicGLn.continuous_det K n))) hk

theorem map_vecMul_diagonal (d : Fin n → IdeleGroup K) :
    (adeleMeasurePi K).map (fun x => x ᵥ* Matrix.diagonal (fun i => (d i : 𝔸[K]))) =
      (∏ i, ENNReal.ofReal ((IdeleGroup.ideleModule K (d i) : ℝ))⁻¹) •
        adeleMeasurePi K (ι := Fin n) := by
  have hf : (fun x : Fin n → 𝔸[K] => x ᵥ* Matrix.diagonal (fun i => (d i : 𝔸[K]))) =
      fun x i => d i • x i := by
    funext x i
    rw [vecMul_diagonal, Units.smul_def, smul_eq_mul, mul_comm]
  have hsm : ∀ i, Measurable fun y : 𝔸[K] => d i • y := fun i =>
    (Homeomorph.smul (d i)).continuous.measurable
  have hmeas : Measurable fun x : Fin n → 𝔸[K] => fun i => d i • x i :=
    measurable_pi_lambda _ fun i => (hsm i).comp (measurable_pi_apply i)
  set c : Fin n → ℝ≥0 := fun i => Real.toNNReal ((IdeleGroup.ideleModule K (d i) : ℝ))⁻¹
  have hc : ∀ i, ENNReal.ofReal ((IdeleGroup.ideleModule K (d i) : ℝ))⁻¹ = (c i : ℝ≥0∞) :=
    fun i => rfl
  have hmap : ∀ i, (adeleMeasure K).map (fun y => d i • y) = c i • adeleMeasure K := by
    intro i
    rw [map_smul_adeleMeasure, hc, ENNReal.smul_def]
  have h1 : (adeleMeasurePi K).map (fun x : Fin n → 𝔸[K] => fun i => d i • x i) =
      Measure.pi fun i => c i • adeleMeasure K := by
    refine (pi_eq fun s hs => ?_).symm
    rw [map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun x : Fin n → 𝔸[K] => fun i => d i • x i) ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => (fun y => d i • y) ⁻¹' s i := by
      ext x
      simp
    rw [hpre, adeleMeasurePi, pi_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hmap i, map_apply (hsm i) (hs i)]
  have h2 : (Measure.pi fun i => c i • adeleMeasure K) =
      (∏ i, c i) • adeleMeasurePi K (ι := Fin n) := by
    refine pi_eq fun s hs => ?_
    rw [Measure.smul_apply, adeleMeasurePi, pi_pi, ENNReal.smul_def, smul_eq_mul,
      ENNReal.ofNNReal_finsetProd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [hf, h1, h2, ENNReal.smul_def, ENNReal.ofNNReal_finsetProd]
  simp only [hc]

theorem map_vecMul_adelicBorel' {b : GL (Fin n) 𝔸[K]}
    (hb : b ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL K n))) :
    (adeleMeasurePi K).map (fun x => x ᵥ* (b : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ENNReal.ofReal ((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ))⁻¹ •
        adeleMeasurePi K (ι := Fin n) := by
  set M : Matrix (Fin n) (Fin n) 𝔸[K] := ↑b
  have hup : M.IsUpperTriangular := hb
  set d : Fin n → IdeleGroup K := fun i => (isUnit_apply_self_of_mem_adelicBorel hb i).unit
  have hd : ∀ i, (d i : 𝔸[K]) = M i i := fun i => IsUnit.unit_spec _
  set D : Matrix (Fin n) (Fin n) 𝔸[K] := Matrix.diagonal fun i => (d i : 𝔸[K])
  set Dinv : Matrix (Fin n) (Fin n) 𝔸[K] := Matrix.diagonal fun i => ((d i)⁻¹ : IdeleGroup K)
  set u : Matrix (Fin n) (Fin n) 𝔸[K] := Dinv * M
  have hDD : D * Dinv = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hM : M = D * u := by rw [← Matrix.mul_assoc, hDD, Matrix.one_mul]
  have hlow : ∀ i j : Fin n, j < i → u i j = 0 := by
    intro i j hij
    show (Dinv * M) i j = 0
    rw [Matrix.diagonal_mul, hup hij, mul_zero]
  have hdiag : ∀ i, u i i = 1 := by
    intro i
    show (Dinv * M) i i = 1
    rw [Matrix.diagonal_mul, ← hd, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) =
      ∏ i, IdeleGroup.ideleModule K (d i) := by
    rw [← map_prod]
    congr 1
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod]
    show M.det = _
    rw [Matrix.det_of_isUpperTriangular hup]
    exact Finset.prod_congr rfl fun i _ => (hd i).symm
  have hcomp : (fun x : Fin n → 𝔸[K] => x ᵥ* M) =
      (fun x => x ᵥ* u) ∘ (fun x => x ᵥ* D) := by
    funext x
    simp only [Function.comp_apply, hM, vecMul_vecMul]
  have hmu : MeasurePreserving (fun x : Fin n → 𝔸[K] => x ᵥ* u) (adeleMeasurePi K)
      (adeleMeasurePi K) :=
    measurePreserving_vecMul_unitriangular (adeleMeasure K) u hlow hdiag
  have hDm : Measurable fun x : Fin n → 𝔸[K] => x ᵥ* D :=
    (continuous_id.matrix_vecMul continuous_const).measurable
  rw [hcomp, ← map_map hmu.measurable hDm, map_vecMul_diagonal, Measure.map_smul, hmu.map_eq,
    hdet]
  congr 1
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => inv_nonneg.2 (IdeleGroup.ideleModule K (d i)).2.le),
    Finset.prod_inv_distrib, coe_finset_prod_pos]

theorem map_vecMul_adeleMeasurePi (g : GL (Fin n) 𝔸[K]) :
    (adeleMeasurePi K).map (fun x => x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ENNReal.ofReal ((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det g) : ℝ))⁻¹ •
        adeleMeasurePi K (ι := Fin n) := by
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_adelicBorel_mul_maxCompact (K := K) (n := n) g
  have hcomp : (fun x : Fin n → 𝔸[K] =>
      x ᵥ* ((b * k : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])) =
      (fun x => x ᵥ* (k : Matrix (Fin n) (Fin n) 𝔸[K])) ∘
        (fun x => x ᵥ* (b : Matrix (Fin n) (Fin n) 𝔸[K])) := by
    funext x
    simp only [Function.comp_apply, Units.val_mul, vecMul_vecMul]
  rw [hcomp, ← map_map (measurable_vecMul' k) (measurable_vecMul' b), map_vecMul_adelicBorel' hb,
    Measure.map_smul, map_vecMul_maxCompact' hk, map_mul, map_mul,
    ideleModule_det_of_mem_maxCompact' hk, mul_one]

end

end GroundTheory.Automorphic.GJGlobal.Modulus
