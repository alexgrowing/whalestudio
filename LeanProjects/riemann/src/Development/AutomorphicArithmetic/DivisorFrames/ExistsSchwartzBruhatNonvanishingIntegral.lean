import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AutomorphicArithmetic.DivisorFrames.FourierSchwartzBruhatPreserved
import Development.AutomorphicArithmetic.DivisorFrames.HaarIntegralUnitsScaling
import Development.AutomorphicArithmetic.DivisorFrames.FiniteUnitContractions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAbsPowerLocallyConstant
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

private theorem UpperTheory.exists_test_function_killing_fixed_points {A : Type} [CommRing A] (P : (A → ℂ) → Prop) (Φ : (A → ℂ) → A → ℂ) (S : Finset Aˣ)
    (h0 : ∃ T, P T) (hD : ∀ u ∈ S, ∀ T, P T → ∃ T', P T' ∧ ∀ t, Φ T' t = Φ T t - Φ T (u * t)) :
    ∃ T, P T ∧ ∀ u ∈ S, ∀ t, (u : A) * t = t → Φ T t = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => obtain ⟨T, hT⟩ := h0; exact ⟨T, hT, by simp⟩
  | insert a S _ ih =>
    obtain ⟨T, hT, hv⟩ := ih fun u hu => hD u (Finset.mem_insert_of_mem hu)
    obtain ⟨T', hT', e⟩ := hD a (Finset.mem_insert_self _ _) T hT
    refine ⟨T', hT', fun u hu t ht => ?_⟩
    rw [e]
    rcases Finset.mem_insert.1 hu with rfl | hu
    · rw [ht, sub_self]
    · rw [hv u hu t ht, hv u hu (a * t) (by rw [mul_left_comm, ht]), sub_self]

private theorem UpperTheory.exists_locally_constant_test_function {G A : Type} [TopologicalSpace G] [TopologicalSpace A] [T2Space A] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (j : G → A) (hj : IsOpenEmbedding j) (χ : G → ℂ) (hχ : IsLocallyConstant χ) (U : Set G) (hc : IsCompact U)
    (ho : IsOpen U) (x : G) (hx : x ∈ U) (h1 : χ x = 1) :
    ∃ T : A → ℂ, IsLocallyConstant T ∧ HasCompactSupport T ∧ ∫ l, T (j l) * χ l ∂μ ≠ 0 := by
  set V : Set G := U ∩ {l | χ l = 1} with hV
  have hf := hχ.isClopen_fiber 1
  have hVc : IsCompact V := hc.inter_right hf.1
  have hVo : IsOpen V := ho.inter hf.2
  have hWc : IsCompact (j '' V) := hVc.image hj.continuous
  have hW : IsClopen (j '' V) := ⟨hWc.isClosed, hj.isOpenMap _ hVo⟩
  refine ⟨(j '' V).indicator 1, (LocallyConstant.charFn ℂ hW).isLocallyConstant,
    HasCompactSupport.intro hWc fun y hy => Set.indicator_of_notMem hy _, ?_⟩
  have e : (fun l => (j '' V).indicator (1 : A → ℂ) (j l) * χ l) = V.indicator fun _ => (1 : ℂ) := by
    funext l
    by_cases h : l ∈ V
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_image_of_mem j h), show χ l = 1 from h.2]
      simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (by rwa [hj.injective.mem_set_image]), zero_mul]
  rw [e, integral_indicator_const _ hVo.measurableSet]
  have : μ.real V ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨hVo.measure_ne_zero μ ⟨x, hx, h1⟩, hVc.measure_lt_top.ne⟩
  simpa using this

theorem UpperTheory.exists_schwartz_bruhat_nonvanishing_integral :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
        ∀ [MeasurableSpace (Fv F v ⊗[F] E)] [BorelSpace (Fv F v ⊗[F] E)] (m : Measure (Fv F v ⊗[F] E)) [m.IsAddHaarMeasure],
        ∀ (μ : Measure (idelesAt E (evFin F v))), IsNormE E v μ → ∀ (ν : Chr F E), Continuous ν → ∀ z : ℕ, 2 ≤ z →
        ∃ T ∈ SB (Fv F v ⊗[F] E), ∃ C : Set (idelesAt E (evFin F v)), IsCompact C ∧
          (∀ t, four v ψ m T t ≠ 0 → ∃ l ∈ C, compFin F E v (l.1 : AE F E) = t) ∧
          (∫ l : idelesAt E (evFin F v), T (compFin F E v (l.1 : AE F E)) * (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z ∂μ) ≠ 0 := by
  intro F E _ _ _ _ _ v ψ hc hψ _ _ m _ μ hμ ν hν z hz
  haveI := GlobalTheory.LocTateInt.isTopologicalRing_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.t2Space_Fv_tensor (E := E) v
  haveI := GlobalTheory.LocTateInt.isModuleTopology_Ev (E := E) v
  haveI := GlobalTheory.LocTateInt.isOpenUnits_Ev (E := E) v
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := hμ.1
  set φ := idelesAtEquiv E v with hφ
  let j : idelesAt E (evFin F v) → Fv F v ⊗[F] E := fun l => compFin F E v (l.1 : AE F E)
  have hoe : IsOpenEmbedding j :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := Fv F v ⊗[F] E)).comp φ.toHomeomorph.isOpenEmbedding
  have hjφ : ∀ l, j l = ((φ l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := fun l => rfl
  let χ : idelesAt E (evFin F v) → ℂ := fun l => (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z
  have hχ : IsLocallyConstant χ := GlobalTheory.LocConstChar.isLocallyConstant_char_absPow F E ν hν z v
  have hχm : ∀ a b, χ (a * b) = χ a * χ b := fun a b => by
    simp only [χ, Subgroup.coe_mul, map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_pow]
    ring
  have hint : ∀ T : Fv F v ⊗[F] E → ℂ, IsLocallyConstant T → HasCompactSupport T →
      Integrable (fun l => T (j l) * χ l) μ := by
    intro T hl hT
    obtain ⟨R, hR⟩ := hT.isCompact.exists_bound_of_continuousOn hl.continuous.continuousOn
    have hI := (GlobalTheory.LocTateInt.integrable_indicator_absE_pow v μ hμ _ hT.isCompact z (by omega)).const_mul R
    refine hI.mono' ((hl.continuous.comp hoe.continuous).mul hχ.continuous).aestronglyMeasurable
      (ae_of_all _ fun l => ?_)
    by_cases h : j l ∈ tsupport T
    · rw [Set.indicator_of_mem h]
      simp only [χ, norm_mul, norm_pow, Circle.norm_coe, one_mul, Complex.norm_real, NNReal.norm_eq]
      exact mul_le_mul_of_nonneg_right (hR _ h) (by positivity)
    · rw [Set.indicator_of_notMem h, image_eq_zero_of_notMem_tsupport h]
      simp
  have hintF : ∀ T : Fv F v ⊗[F] E → ℂ, IsLocallyConstant T → HasCompactSupport T → ∀ t,
      Integrable (fun s => T s * ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s))) m := by
    intro T hl hT t
    refine Continuous.integrable_of_hasCompactSupport (hl.continuous.mul (hc.comp
      ((IsModuleTopology.continuous_of_linearMap (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))).comp
        (continuous_const.mul continuous_id)))) hT.mul_right
  obtain ⟨S, hS1, hS2⟩ := UpperTheory.finite_unit_contractions F E v
  obtain ⟨hUc, hUo⟩ := isCompact_isOpen_unitsAt (E := E) v
  obtain ⟨T, ⟨hl, hT, hZ⟩, hv⟩ := UpperTheory.exists_test_function_killing_fixed_points
    (fun T => IsLocallyConstant T ∧ HasCompactSupport T ∧ ∫ l, T (j l) * χ l ∂μ ≠ 0) (four v ψ m) S
    (UpperTheory.exists_locally_constant_test_function μ j hoe χ hχ _ hUc hUo 1 (one_mem (unitsAt E v)) (by simp [χ])) (by
      rintro u hu T ⟨hl, hT, hZ⟩
      set a : ℝ≥0 := GlobalTheory.Doubling.absEv F E v u with ha
      have ha0 : a ≠ 0 := fun h => by
        have e := congrArg (GlobalTheory.Doubling.absEv F E v) (mul_inv_cancel u)
        rw [map_mul, map_one, ← ha, h, zero_mul] at e
        exact zero_ne_one e
      let T₁ : Fv F v ⊗[F] E → ℂ := fun s => T ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) * s)
      have hl₁ : IsLocallyConstant T₁ := hl.comp_continuous (continuous_const.mul continuous_id)
      have hT₁ : HasCompactSupport T₁ := hT.comp_homeomorph (Homeomorph.smul u⁻¹)
      have hTu : ∀ s, T₁ (u * s) = T s := fun s => by simp only [T₁, Units.inv_mul_cancel_left]
      refine ⟨fun s => T s - (((a : ℝ) : ℂ))⁻¹ * T₁ s, ⟨hl.sub ((IsLocallyConstant.const _).mul hl₁),
        hT.sub hT₁.mul_left, ?_⟩, fun t => ?_⟩
      · have e := integral_mul_left_eq_self (μ := μ) (fun l => T₁ (j l) * χ l) (φ.symm u)
        have e2 : ∀ l, T₁ (j (φ.symm u * l)) * χ (φ.symm u * l) = χ (φ.symm u) * (T (j l) * χ l) := fun l => by
          rw [hjφ, map_mul, ContinuousMulEquiv.apply_symm_apply, Units.val_mul, hTu, hχm, ← hjφ]
          ring
        simp only [e2, integral_const_mul] at e
        simp only [sub_mul, mul_assoc]
        rw [integral_sub (hint T hl hT) ((hint T₁ hl₁ hT₁).const_mul _), integral_const_mul, ← e, ← mul_assoc,
          ← one_sub_mul]
        refine mul_ne_zero (sub_ne_zero.2 fun h => hS1 u hu ?_) hZ
        have hab : absE F E (φ.symm u).1 = a := by
          rw [absE_of_mem (φ.symm u).2]
          exact congrArg _ (φ.apply_symm_apply u)
        have h2 := congrArg norm h
        simp only [χ, hab, norm_one, norm_mul, norm_inv, norm_pow, Circle.norm_coe, one_mul, Complex.norm_real,
          NNReal.norm_eq] at h2
        have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
        rw [← mul_pow_sub_one (show z ≠ 0 by omega), inv_mul_cancel_left₀ ha'] at h2
        have h3 := (pow_eq_one_iff_of_nonneg a.coe_nonneg (show z - 1 ≠ 0 by omega)).1 h2.symm
        exact_mod_cast h3
      · have e := UpperTheory.haar_integral_units_scaling F E v m u fun s => T₁ s * ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s))
        simp only [four, sub_mul, mul_assoc]
        rw [integral_sub (hintF T hl hT t) ((hintF T₁ hl₁ hT₁ t).const_mul _), integral_const_mul, ← e]
        simp only [hTu, mul_left_comm t])
  obtain ⟨hFl, hFc⟩ := UpperTheory.fourier_schwartz_bruhat_preserved F E v ψ hc hψ m T ⟨hl, hT⟩
  have hcl : IsClosed (Function.support (four v ψ m T)) := (hFl.isClopen_fiber 0).2.isClosed_compl
  have hsc : IsCompact (Function.support (four v ψ m T)) := by
    rw [← hcl.closure_eq]; exact hFc
  have hsub : Function.support (four v ψ m T) ⊆ Set.range j := by
    intro t ht
    by_cases hu : IsUnit t
    · exact ⟨φ.symm hu.unit, by rw [hjφ, ContinuousMulEquiv.apply_symm_apply, hu.unit_spec]⟩
    · obtain ⟨u, hu, e⟩ := hS2 t hu
      exact absurd (hv u hu t e) ht
  refine ⟨T, ⟨hl, hT⟩, j ⁻¹' Function.support (four v ψ m T), hoe.isInducing.isCompact_preimage' hsc hsub,
    fun t ht => ?_, ?_⟩
  · obtain ⟨l, rfl⟩ := hsub ht
    exact ⟨l, ht, rfl⟩
  · simpa only [mul_assoc] using hZ
