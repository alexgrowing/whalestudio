import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContinuous
import GroundTheory.AutomorphicForms.GKModules.KernelCalculus
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract

open MeasureTheory Set Filter Topology Function

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open AutomorphicForm RightCosetSpace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => Reduction.rationalGLOne K n

theorem retractOne_mul (g h : AdelicGLn.AdelicGL K n) :
    retractOne (g * h) = retractOne g * retractOne h := by
  ext1
  rw [coe_retractOne, Subgroup.coe_mul, coe_retractOne, coe_retractOne, map_mul,
    mul_comm (detModule K n g), map_mul, mul_inv_rev]
  simp only [mul_assoc]
  rw [← mul_assoc h (centralSection K n (detModule K n g))⁻¹,
    ← centralSection_inv_mul_comm (detModule K n g) h,
    mul_assoc (centralSection K n (detModule K n g))⁻¹]

theorem retractOne_coe (x : normOneGL K n) : retractOne (x : AdelicGLn.AdelicGL K n) = x := by
  ext1
  rw [coe_retractOne, (mem_normOneGL_iff_detModule).1 x.2, map_one, inv_one, mul_one]

theorem retractOne_mul_coe (g : AdelicGLn.AdelicGL K n) (x : normOneGL K n) :
    retractOne (g * (x : AdelicGLn.AdelicGL K n)) = retractOne g * x := by
  rw [retractOne_mul, retractOne_coe]

theorem retractOne_coe_mul (x : normOneGL K n) (g : AdelicGLn.AdelicGL K n) :
    retractOne ((x : AdelicGLn.AdelicGL K n) * g) = x * retractOne g := by
  rw [retractOne_mul, retractOne_coe]

theorem retractOne_mul_infEmb (g : AdelicGLn.AdelicGL K n) (a : archGroup K n) :
    retractOne (g * infEmb K n a) = retractOne g * archP K n a := by
  rw [retractOne_mul, retract_infEmb]

theorem retractOne_centralSection (s : {r : ℝ // 0 < r}) : retractOne (centralSection K n s) = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))
  · ext1
    rw [coe_retractOne, detModule_centralSection hn, mul_inv_cancel]
    rfl

def liftOne (F : normOneGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ := F (retractOne g)

theorem liftOne_coe (F : normOneGL K n → ℂ) (x : normOneGL K n) :
    liftOne F (x : AdelicGLn.AdelicGL K n) = F x := by
  rw [liftOne, retractOne_coe]

theorem liftOne_centralSection_mul (F : normOneGL K n → ℂ) (s : {r : ℝ // 0 < r})
    (g : AdelicGLn.AdelicGL K n) : liftOne F (centralSection K n s * g) = liftOne F g := by
  rw [liftOne, liftOne, retractOne_mul, retractOne_centralSection, one_mul]

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem exists_isContRep_of_mem_span {X : Set (Lp ℂ 2 (quotientMeasure Γ₁ μ))}
    (hX : ∀ x ∈ X, ∃ F, IsContRep μ x F) {w : Lp ℂ 2 (quotientMeasure Γ₁ μ)}
    (hw : w ∈ Submodule.span ℂ X) : ∃ F, IsContRep μ w F := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hX x hx
  | zero => exact ⟨0, isContRep_zero⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF⟩ := hx
    obtain ⟨G, hG⟩ := hy
    exact ⟨F + G, hF.add hG⟩
  | smul c x _ hx =>
    obtain ⟨F, hF⟩ := hx
    exact ⟨c • F, hF.smul c⟩

theorem finiteDimensional_span_liftOne (W : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ₁ μ)))
    [FiniteDimensional ℂ W] (hW : ∀ w ∈ W, ∃ F, IsContRep μ w F)
    (S : Set (AdelicGLn.AdelicGL K n → ℂ))
    (hS : ∀ f ∈ S, ∃ w ∈ W, ∃ F, IsContRep μ w F ∧ f = liftOne F) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  classical
  choose R hR using fun w : W => hW w w.2
  let T : W →ₗ[ℂ] (AdelicGLn.AdelicGL K n → ℂ) :=
    { toFun := fun w => liftOne (R w)
      map_add' := fun w₁ w₂ => by
        have e : R (w₁ + w₂) = R w₁ + R w₂ :=
          (hR (w₁ + w₂)).unique (((hR w₁).add (hR w₂)).of_eq (Submodule.coe_add w₁ w₂).symm)
        funext g
        simp only [liftOne, e, Pi.add_apply]
      map_smul' := fun c w => by
        have e : R (c • w) = c • R w :=
          (hR (c • w)).unique (((hR w).smul c).of_eq (Submodule.coe_smul c w).symm)
        funext g
        simp only [liftOne, e, Pi.smul_apply, RingHom.id_apply] }
  have hle : Submodule.span ℂ S ≤ LinearMap.range T := by
    rw [Submodule.span_le]
    intro f hf
    obtain ⟨w, hw, F, hF, rfl⟩ := hS f hf
    refine ⟨⟨w, hw⟩, ?_⟩
    show liftOne (R ⟨w, hw⟩) = liftOne F
    rw [(hR ⟨w, hw⟩).unique hF]
  exact Submodule.finiteDimensional_of_le hle

variable (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]

theorem eq_integral_of_integrated_eq {v : CuspL2 μ} {Φ : normOneGL K n → ℂ}
    (hrep : IsContRep μ (toLp μ v) Φ) {C : ℝ} (hb : ∀ y, ‖Φ y‖ ≤ C) {κ : archGroup K n → ℂ}
    (hκt : (isExpLieAlgebra K n).IsTestFunction κ) (hκv : (archRepT μ).integrated ν κ v = v)
    (y : normOneGL K n) : Φ y = ∫ a, κ a * Φ (y * archP K n a) ∂ν :=
  congrFun (hrep.unique ((isContRep_integrated_archRepT μ ν hrep hb hκt.continuous hκt.2).of_eq
    (congrArg (toLp μ) hκv))) y

omit [μ.IsHaarMeasure] in

theorem slice_eq_integral {Φ : normOneGL K n → ℂ} {κ : archGroup K n → ℂ}
    (hΦκ : ∀ y, Φ y = ∫ a, κ a * Φ (y * archP K n a) ∂ν) (y : normOneGL K n) :
    (fun x : archGroup K n => Φ (y * archP K n x)) =
      fun x => ∫ a, (fun x : archGroup K n => Φ (y * archP K n x)) (x * a) * κ a ∂ν := by
  funext x
  refine (hΦκ (y * archP K n x)).trans (integral_congr_ae (Eventually.of_forall fun a => ?_))
  show κ a * Φ (y * archP K n x * archP K n a) = Φ (y * archP K n (x * a)) * κ a
  rw [map_mul, mul_assoc y, mul_comm]

omit [μ.IsHaarMeasure] in

theorem isSmoothFun_slice {Φ : normOneGL K n → ℂ} (hΦc : Continuous Φ) {κ : archGroup K n → ℂ}
    (hκt : (isExpLieAlgebra K n).IsTestFunction κ)
    (hΦκ : ∀ y, Φ y = ∫ a, κ a * Φ (y * archP K n a) ∂ν) (y : normOneGL K n) :
    (isExpLieAlgebra K n).IsSmoothFun (fun x : archGroup K n => Φ (y * archP K n x)) := by
  have hΨ : Continuous (fun x : archGroup K n => Φ (y * archP K n x)) :=
    hΦc.comp (continuous_const.mul continuous_archP)
  rw [slice_eq_integral ν hΦκ y]
  exact (isExpLieAlgebra K n).isSmoothFun_integral_mul ν hΨ hκt

theorem exists_uAction_slice {v : CuspL2 μ} (hs : (isExpLieAlgebra K n).IsSmoothVector (archRepT μ) v)
    {Φ : normOneGL K n → ℂ} (hΦc : Continuous Φ) {κ : archGroup K n → ℂ}
    (hκt : (isExpLieAlgebra K n).IsTestFunction κ) (hκv : (archRepT μ).integrated ν κ v = v)
    (hΦκ : ∀ y, Φ y = ∫ a, κ a * Φ (y * archP K n a) ∂ν) (u : UEnv K n) :
    ∃ γ : archGroup K n → ℂ, (isExpLieAlgebra K n).IsTestFunction γ ∧
      ((isExpLieAlgebra K n).uAction (archRepT μ) u ⟨v, hs⟩ : CuspL2 μ) =
        (archRepT μ).integrated ν γ v ∧
      ∀ y : normOneGL K n, ((isExpLieAlgebra K n).rightUAction (F := ℂ) u
          ⟨fun x => Φ (y * archP K n x), isSmoothFun_slice ν hΦc hκt hΦκ y⟩ : archGroup K n → ℂ) =
        fun x => ∫ a, Φ (y * archP K n (x * a)) * γ a ∂ν := by
  obtain ⟨γ, hγ, hvec, hfun⟩ := (isExpLieAlgebra K n).exists_uAction_integrated ν (archRepT μ) u hκt
  refine ⟨γ, hγ, ?_, fun y => ?_⟩
  · have e : (⟨v, hs⟩ : (isExpLieAlgebra K n).smoothVectors (archRepT μ)) =
        ⟨(archRepT μ).integrated ν κ v,
          (isExpLieAlgebra K n).isSmoothVector_integrated (archRepT μ) ν hκt v⟩ :=
      Subtype.ext hκv.symm
    exact (congrArg (fun w => ((isExpLieAlgebra K n).uAction (archRepT μ) u w : CuspL2 μ)) e).trans
      (hvec v)
  · have hΨ : Continuous (fun x : archGroup K n => Φ (y * archP K n x)) :=
      hΦc.comp (continuous_const.mul continuous_archP)
    have e : (⟨fun x => Φ (y * archP K n x), isSmoothFun_slice ν hΦc hκt hΦκ y⟩ :
        (isExpLieAlgebra K n).smoothFuns (F := ℂ)) =
        ⟨fun g => ∫ a, (fun x : archGroup K n => Φ (y * archP K n x)) (g * a) * κ a ∂ν,
          (isExpLieAlgebra K n).isSmoothFun_integral_mul ν hΨ hκt⟩ :=
      Subtype.ext (slice_eq_integral ν hΦκ y)
    exact (congrArg (fun f => ((isExpLieAlgebra K n).rightUAction (F := ℂ) u f :
      archGroup K n → ℂ)) e).trans (hfun _ hΨ)

def IsZKFinite (v : CuspL2 μ) : Prop :=
  ∃ hs : (isExpLieAlgebra K n).IsSmoothVector (archRepT μ) v,
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k :
      (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v)) ∧
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z => (isExpLieAlgebra K n).uAction (archRepT μ) z
      ⟨v, hs⟩) '' ((isExpLieAlgebra K n).centerU : Set _)))

set_option maxHeartbeats 1000000 in

theorem exists_cuspForm_of_isZKFinite (v : CuspL2 μ) (hv : IsZKFinite μ v) :
    ∃ φ : cuspForms K n,
      ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) = toLp μ v ∧
      ∀ (s : {r : ℝ // 0 < r}) (g : AdelicGLn.AdelicGL K n),
        (φ : AdelicGLn.AdelicGL K n → ℂ) (centralSection K n s * g) = (φ : AdelicGLn.AdelicGL K n → ℂ) g := by
  obtain ⟨hs, hK, hZ⟩ := hv
  have hνH : (Measure.haar : Measure (archGroup K n)).IsHaarMeasure := inferInstance
  obtain ⟨κ, U, Φ, C, hκt, hκv, hU, hrep, hb, hΦU, hcusp⟩ :=
    exists_contRep_of_zkFinite μ Measure.haar v hs hK hZ
  have hΦκ := eq_integral_of_integrated_eq μ Measure.haar hrep hb hκt hκv

  have hslice : ∀ g, archSlice (liftOne Φ) g = fun x => Φ (retractOne g * archP K n x) :=
    fun g => funext fun x => by
      rw [archSlice_apply, liftOne, retractOne_mul_infEmb]
  have hsm : IsArchSmooth (liftOne Φ) := fun g => by
    rw [hslice g]
    exact isSmoothFun_slice Measure.haar hrep.1 hκt hΦκ _

  have hfin : ∀ g, ∀ᶠ y in 𝓝 (1 : AdelicGLn.FiniteAdelicGL K n),
      liftOne Φ (g * finEmb K n y) = liftOne Φ g := by
    intro g
    filter_upwards [(finOpenSubgroup U hU).mem_nhds_one] with y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    show Φ (retractOne (g * finEmb K n (u : AdelicGLn.FiniteAdelicGL K n))) = Φ (retractOne g)
    rw [retractOne_mul_finEmb g u.2]
    exact hΦU u hu _

  have hli : IsLeftInvariant (liftOne Φ) := by
    intro γ g
    have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL K n := rationalGL_le_normOneGL ⟨γ, rfl⟩
    have hγΓ : (⟨AdelicGLn.diagonal K n γ, hγ1⟩ : normOneGL K n) ∈ Γ₁ := ⟨γ, rfl⟩
    exact (congrArg Φ (retractOne_coe_mul ⟨_, hγ1⟩ g)).trans (hrep.2.1 _ hγΓ _)

  have hKf : IsKFinite (liftOne Φ) := by
    unfold IsKFinite
    obtain ⟨W, hWdef⟩ : ∃ W : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ₁ μ)),
        W = Submodule.span ℂ (Set.range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
          toLp μ (cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v)) := ⟨_, rfl⟩
    have hWfin : FiniteDimensional ℂ W := by
      have e : W = (Submodule.span ℂ (Set.range fun k :
          (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
            cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v)).map
              (toLp μ : CuspL2 μ →ₗ[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ)) := by
        rw [hWdef, Submodule.map_span, ← Set.range_comp]
        rfl
      rw [e]
      infer_instance
    have hgen : ∀ k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
        IsContRep μ (toLp μ (cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v))
          (fun y => Φ (y * ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩)) :=
      fun k => (hrep.translate _).of_eq (toLp_cuspRepT μ _ v).symm
    refine finiteDimensional_span_liftOne μ W ?_ _ ?_
    · intro w hw
      rw [hWdef] at hw
      refine exists_isContRep_of_mem_span μ ?_ hw
      rintro _ ⟨k, rfl⟩
      exact ⟨_, hgen k⟩
    · rintro _ ⟨k, rfl⟩
      refine ⟨_, hWdef ▸ Submodule.subset_span ⟨k, rfl⟩, _, hgen k, ?_⟩
      funext g
      show Φ (retractOne (g * (k : AdelicGLn.AdelicGL K n))) = Φ (retractOne g * _)
      rw [← retractOne_mul_coe g ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩]

  have hder : ∀ u : UEnv K n, ∃ F : normOneGL K n → ℂ,
      IsContRep μ (toLp μ ((isExpLieAlgebra K n).uAction (archRepT μ) u ⟨v, hs⟩ : CuspL2 μ)) F ∧
        (uAction u ⟨liftOne Φ, hsm⟩ : AdelicGLn.AdelicGL K n → ℂ) = liftOne F := by
    intro u
    obtain ⟨γ, hγ, hvec, hfun⟩ := exists_uAction_slice μ Measure.haar hs hrep.1 hκt hκv hΦκ u
    refine ⟨fun y => ∫ a, γ a * Φ (y * archP K n a) ∂Measure.haar,
      (isContRep_integrated_archRepT μ Measure.haar hrep hb hγ.continuous hγ.2).of_eq
        (congrArg (toLp μ) hvec).symm, ?_⟩
    funext g
    rw [coe_uAction]
    have e : sliceL g ⟨liftOne Φ, hsm⟩ =
        ⟨fun x => Φ (retractOne g * archP K n x), isSmoothFun_slice Measure.haar hrep.1 hκt hΦκ _⟩ :=
      Subtype.ext (hslice g)
    show ((isExpLieAlgebra K n).rightUAction u (sliceL g ⟨liftOne Φ, hsm⟩) : archGroup K n → ℂ) 1 = _
    rw [e, hfun (retractOne g)]
    show ∫ a, Φ (retractOne g * archP K n (1 * a)) * γ a ∂Measure.haar =
      ∫ a, γ a * Φ (retractOne g * archP K n a) ∂Measure.haar
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show Φ (retractOne g * archP K n (1 * a)) * γ a = γ a * Φ (retractOne g * archP K n a)
    rw [one_mul, mul_comm]

  have hZf : IsZFinite (⟨liftOne Φ, hsm⟩ : archSmooth K n) := by
    unfold IsZFinite
    set X := (fun z => uAction z (⟨liftOne Φ, hsm⟩ : archSmooth K n)) ''
      ((isExpLieAlgebra K n).centerU : Set (UEnv K n)) with hX
    obtain ⟨W, hWdef⟩ : ∃ W : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ₁ μ)),
        W = Submodule.span ℂ ((fun z => toLp μ ((isExpLieAlgebra K n).uAction (archRepT μ) z ⟨v, hs⟩ :
          CuspL2 μ)) '' ((isExpLieAlgebra K n).centerU : Set (UEnv K n))) := ⟨_, rfl⟩
    have hWfin : FiniteDimensional ℂ W := by
      have e : W = (Submodule.span ℂ ((fun z => (isExpLieAlgebra K n).uAction (archRepT μ) z ⟨v, hs⟩) ''
          ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))).map
            ((toLp μ : CuspL2 μ →ₗ[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ)).comp
              ((isExpLieAlgebra K n).smoothVectors (archRepT μ)).subtype) := by
        rw [hWdef, Submodule.map_span, Set.image_image]
        rfl
      rw [e]
      infer_instance
    have hT : Function.Injective (archSmooth K n).subtype := Subtype.val_injective
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ ((archSmooth K n).subtype '' X)) := by
      refine finiteDimensional_span_liftOne μ W ?_ _ ?_
      · intro w hw
        rw [hWdef] at hw
        refine exists_isContRep_of_mem_span μ ?_ hw
        rintro _ ⟨z, -, rfl⟩
        obtain ⟨F, hF, -⟩ := hder z
        exact ⟨F, hF⟩
      · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        obtain ⟨F, hF, hFe⟩ := hder z
        exact ⟨_, hWdef ▸ Submodule.subset_span ⟨z, hz, rfl⟩, F, hF, hFe⟩
    rw [← Submodule.map_span] at hfd
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective (archSmooth K n).subtype hT (Submodule.span ℂ X)).symm

  have hmg : HasModerateGrowth (liftOne Φ) := ⟨C, 0, fun g => by
    rw [pow_zero, mul_one]
    exact hb _⟩

  have hcu : IsCuspidal (liftOne Φ) := by
    intro r hr hrn g
    rw [← hcusp r hr hrn (retractOne g)]
    unfold constantTerm
    refine setIntegral_congr_fun (measurableSet_unipFundamentalDomain (K := K) (n := n) (r := r))
      fun X _ => ?_
    show Φ (retractOne ((unipOne K n r X : AdelicGLn.AdelicGL K n) * g)) = _
    rw [retractOne_coe_mul]
  have haf : IsAutomorphicForm (liftOne Φ) :=
    { isLeftInvariant := hli
      isSmooth := ⟨hsm, hfin⟩
      isKFinite := hKf
      isZFinite := hZf
      hasModerateGrowth := hmg }
  refine ⟨⟨liftOne Φ, haf, hcu⟩, ?_, fun s g => liftOne_centralSection_mul Φ s g⟩
  refine Lp.ext ((coeFn_cuspToL2 μ ⟨liftOne Φ, haf, hcu⟩).trans (EventuallyEq.trans ?_
    hrep.ae_eq_quotFun.symm))
  refine Eventually.of_forall fun q => ?_
  obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
  rw [cuspQuot_mk, quotFun_mk]
  exact liftOne_coe Φ y

theorem exists_cuspToL2_eq_of_isZKFinite (v : cuspidalL2 μ) (hv : IsZKFinite μ v) :
    ∃ φ : cuspForms K n, cuspToL2 μ φ = v ∧
      ∀ (s : {r : ℝ // 0 < r}) (g : AdelicGLn.AdelicGL K n),
        (φ : AdelicGLn.AdelicGL K n → ℂ) (centralSection K n s * g) = (φ : AdelicGLn.AdelicGL K n → ℂ) g := by
  obtain ⟨φ, hφ, hz⟩ := exists_cuspForm_of_isZKFinite μ v hv
  exact ⟨φ, Subtype.ext hφ, hz⟩

theorem isZKFinite_subset_range_cuspToL2 :
    {v : CuspL2 μ | IsZKFinite μ v} ⊆
      (toLp μ) ⁻¹' ((fun φ : cuspForms K n =>
        ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ))) '' Set.univ) := by
  intro v hv
  obtain ⟨φ, hφ, -⟩ := exists_cuspForm_of_isZKFinite μ v hv
  exact ⟨φ, Set.mem_univ _, hφ⟩

theorem exists_cuspForm_of_mem_summand (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V]
    (hV : (cuspRepT μ).IsInvariant V) (_hirr : ((cuspRepT μ).restrict V hV).IsIrreducible)
    {v : CuspL2 μ} (_hvV : v ∈ V) (hv : IsZKFinite μ v) :
    ∃ φ : cuspForms K n,
      ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) = toLp μ v ∧
      ∀ (s : {r : ℝ // 0 < r}) (g : AdelicGLn.AdelicGL K n),
        (φ : AdelicGLn.AdelicGL K n → ℂ) (centralSection K n s * g) = (φ : AdelicGLn.AdelicGL K n → ℂ) g :=
  exists_cuspForm_of_isZKFinite μ v hv

end CuspidalSpectrum

end

end GroundTheory.Automorphic
