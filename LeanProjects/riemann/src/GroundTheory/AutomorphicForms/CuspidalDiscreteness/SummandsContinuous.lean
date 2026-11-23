import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsIsOpenForallCuspRepTFinOneEq
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsMeasure
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsArchConv
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.GKModules.VectorKernel
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable

open MeasureTheory Set Filter Topology Function
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open AutomorphicForm RightCosetSpace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => Reduction.rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem rconv_mul_of_left_inv {f : normOneGL K n → ℂ} {u : normOneGL K n}
    (hf : ∀ x, f (u⁻¹ * x) = f x) (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (x : normOneGL K n) :
    rconv Γ₁ μ f φ (x * u) = rconv Γ₁ μ f φ x := by
  unfold rconv
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show f ((x * u)⁻¹ * y) * _ = f (x⁻¹ * y) * _
  rw [mul_inv_rev, mul_assoc, hf]

theorem archimedeanProjection_maximalCompact (k : archCompact K n) :
    archP K n (k : archGroup K n) =
      ⟨infEmb K n (k : archGroup K n), Reduction.maxCompact_le_normOneGL k.2⟩ :=
  archProj_of_mem (Reduction.maxCompact_le_normOneGL k.2)

variable {μ} in

theorem IsContRep.of_eq {φ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) (e : φ = ψ) : IsContRep μ ψ F := e ▸ h

variable {μ} in

theorem IsContRep.of_eq_fun {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F G : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) (e : F = G) : IsContRep μ φ G := e ▸ h

omit [μ.IsHaarMeasure] in

theorem smul_comb {E : Type*} [AddCommGroup E] [Module ℂ E] (X : E) (r i c : ℂ) :
    r • (c • X) + Complex.I • (i • (c • X)) = c • ((r + i * Complex.I) • X) := by
  simp only [smul_smul, ← add_smul]
  congr 1
  ring

variable (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]

set_option maxHeartbeats 1000000 in

theorem exists_contRep_of_zkFinite (v : CuspL2 μ)
    (hs : (isExpLieAlgebra K n).IsSmoothVector (archRepT μ) v)
    (hK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k :
      (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v)))
    (hZ : FiniteDimensional ℂ (Submodule.span ℂ ((fun z => (isExpLieAlgebra K n).uAction (archRepT μ) z
      ⟨v, hs⟩) '' ((isExpLieAlgebra K n).centerU : Set _)))) :
    ∃ (κ : archGroup K n → ℂ) (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (Φ : normOneGL K n → ℂ)
      (C : ℝ), (isExpLieAlgebra K n).IsTestFunction κ ∧ (archRepT μ).integrated ν κ v = v ∧
      IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
      IsContRep μ (toLp μ v) Φ ∧ (∀ y, ‖Φ y‖ ≤ C) ∧
      (∀ u ∈ U, ∀ x, Φ (x * finOne K n u) = Φ x) ∧
      ∀ r : ℕ, 0 < r → r < n → ∀ x : normOneGL K n,
        ∫ X in unipFundamentalDomain K n r, Φ (unipOne K n r X * x) ∂unipMeasure K n r = 0 := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ

  have hKarch : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : archCompact K n =>
      archRepT μ (k : archGroup K n) v)) := by
    have hle : Set.range (fun k : archCompact K n => archRepT μ (k : archGroup K n) v) ⊆
        Set.range fun k : (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
          cuspRepT μ ⟨k, Reduction.maxCompact_le_normOneGL k.2⟩ v := by
      rintro _ ⟨k, rfl⟩
      exact ⟨⟨_, k.2⟩, (congrArg (fun g => cuspRepT μ g v) (archimedeanProjection_maximalCompact k)).symm⟩
    exact Submodule.finiteDimensional_of_le (Submodule.span_mono hle)

  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hKc⟩ := exists_archCartanData K n
  obtain ⟨κ, hκt, -, hκv⟩ := (isExpLieAlgebra K n).exists_integrated_eq_of_zkFinite (archRepT μ) ν
    (archCompact K n) B b ε hε horth hsymm hinv hKc ⟨v, hs⟩ hKarch hZ Filter.univ_mem

  obtain ⟨U, hU, hUv⟩ := exists_isOpen_forall_cuspRepT_finOne_eq μ v hK

  obtain ⟨F₀, c, hc, hF₀U, hF₀⟩ := exists_cc_integral_mul_eq μ ν U hU κ hκt.continuous hκt.2
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hint : Integrable (fun a => κ a • archRepT μ a v) ν :=
    integrable_smul_archRepT μ ν hκt.continuous hκt.2 v

  have hRv : (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ F₀) v = (c : ℂ) • v := by
    refine ext_inner_left ℂ fun w => ?_
    have hΘc : Continuous fun x : normOneGL K n => ⟪w, cuspRepT μ x v⟫_ℂ :=
      continuous_const.inner ((cuspRepT μ).continuous_orbit v)
    have hΘU : ∀ u ∈ U, ∀ x, ⟪w, cuspRepT μ (x * finOne K n u) v⟫_ℂ = ⟪w, cuspRepT μ x v⟫_ℂ :=
      fun u hu x => congrArg (fun z => ⟪w, z⟫_ℂ)
        (((cuspRepT μ).map_mul_apply x _ v).trans (congrArg (fun z => cuspRepT μ x z) (hUv u hu)))
    have e1 : ∫ a, κ a * ⟪w, cuspRepT μ (archP K n a) v⟫_ℂ ∂ν = ⟪w, v⟫_ℂ :=
      calc ∫ a, κ a * ⟪w, cuspRepT μ (archP K n a) v⟫_ℂ ∂ν
          = ∫ a, ⟪w, κ a • archRepT μ a v⟫_ℂ ∂ν :=
            integral_congr_ae (Eventually.of_forall fun a =>
              (inner_smul_right w (archRepT μ a v) (κ a)).symm)
        _ = ⟪w, (archRepT μ).integrated ν κ v⟫_ℂ := integral_inner hint w
        _ = ⟪w, v⟫_ℂ := congrArg (fun z => ⟪w, z⟫_ℂ) hκv
    calc ⟪w, (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ F₀) v⟫_ℂ
        = ∫ g, F₀ g * ⟪w, cuspRepT μ g v⟫_ℂ ∂μ := inner_integrated_ccToL1_eq (cuspRepT μ) μ F₀ w v
      _ = (c : ℂ) * ∫ a, κ a * ⟪w, cuspRepT μ (archP K n a) v⟫_ℂ ∂ν := hF₀ _ hΘc hΘU
      _ = (c : ℂ) * ⟪w, v⟫_ℂ := congrArg (fun t => (c : ℂ) * t) e1
      _ = ⟪w, (c : ℂ) • v⟫_ℂ := (inner_smul_right w v (c : ℂ)).symm

  have hsub : ∀ f : CompactlySupportedContinuousMap (normOneGL K n) ℂ,
      (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) (toLp μ v) =
        toLp μ ((cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ f) v) := fun f =>
    (toLp_integrated μ (UnitaryRep.ccToL1 μ f) v).symm
  have hrep0 : IsContRep μ ((c : ℂ) • toLp μ v) (rconv Γ₁ μ F₀ (toLp μ v)) :=
    (isContRep_rconv μ F₀ (toLp μ v)).of_eq
      ((hsub F₀).trans ((congrArg (toLp μ) hRv).trans ((toLp μ).map_smul (c : ℂ) v)))
  have hcancel : ∀ x : Lp ℂ 2 (quotientMeasure Γ₁ μ), (c : ℂ)⁻¹ • (c : ℂ) • x = x := fun x => by
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : normOneGL K n → ℂ,
      Φ = (c : ℂ)⁻¹ • rconv Γ₁ μ F₀ (toLp μ v) := ⟨_, rfl⟩
  have hrep : IsContRep μ (toLp μ v) Φ :=
    ((hrep0.smul (c : ℂ)⁻¹).of_eq (hcancel _)).of_eq_fun hΦ.symm

  obtain ⟨βr, βi, hr, hrc, hru, hi, hic, hiu, hκβ⟩ := exists_real_parts_of_isTestFunction hκt
  obtain ⟨νA, hνA⟩ : ∃ νA : Measure (ArchUnits K n),
      νA = ν.map (fun a : archGroup K n => (a : ArchUnits K n)) := ⟨_, rfl⟩
  have : νA.IsHaarMeasure := hνA ▸ isHaarMeasure_map_val ν
  obtain ⟨Br, hBr⟩ := exists_norm_rconv_le_uniform μ νA hr hrc hru U hU F₀
  obtain ⟨Bi, hBi⟩ := exists_norm_rconv_le_uniform μ νA hi hic hiu U hU F₀
  obtain ⟨fr, hfr⟩ : ∃ fr, fr = archConv νA hr.continuous hrc hru (finAvg U hU F₀) := ⟨_, rfl⟩
  obtain ⟨fi, hfi⟩ : ∃ fi, fi = archConv νA hi.continuous hic hiu (finAvg U hU F₀) := ⟨_, rfl⟩
  have hfin : (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ (finAvg U hU F₀)) v = (c : ℂ) • v :=
    (congrArg (fun g => (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ g) v)
      (finAvg_eq_self U hU hF₀U)).trans hRv
  have hpart : ∀ {β : ArchMatrix K n → ℝ} (hβ : Continuous β) (hβc : HasCompactSupport β)
      (hβu : tsupport β ⊆ Set.range (Units.val : ArchUnits K n → ArchMatrix K n)),
      (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ (archConv νA hβ hβc hβu (finAvg U hU F₀))) v =
        ∫ A, (β A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA := by
    intro β hβ hβc hβu
    exact (integrated_archConv (cuspRepT μ) μ νA hβ hβc hβu (finAvg U hU F₀) v).trans
      (integral_congr_ae (Eventually.of_forall fun A =>
        congrArg (fun z => (β A : ℂ) • cuspRepT μ (archProj K n A) z) hfin))
  have hIr := integrable_smul_archProj (cuspRepT μ) νA hr.continuous hrc hru ((c : ℂ) • v)
  have hIi := integrable_smul_archProj (cuspRepT μ) νA hi.continuous hic hiu ((c : ℂ) • v)
  have hpt : ∀ A : ArchUnits K n, (βr A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) +
      Complex.I • ((βi A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v)) =
        (c : ℂ) • (((βr A : ℂ) + (βi A : ℂ) * Complex.I) • cuspRepT μ (archProj K n A) v) := by
    intro A
    have hms : cuspRepT μ (archProj K n A) ((c : ℂ) • v) = (c : ℂ) • cuspRepT μ (archProj K n A) v :=
      (cuspRepT μ (archProj K n A)).map_smul (c : ℂ) v
    exact (congrArg₂ (fun s t => (βr A : ℂ) • s + Complex.I • ((βi A : ℂ) • t)) hms hms).trans
      (smul_comb _ _ _ _)
  have hcomb : (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fr) v +
      Complex.I • (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fi) v = (c : ℂ) • v := by
    have e1 : (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fr) v +
        Complex.I • (cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fi) v =
        ∫ A, (βr A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA +
          Complex.I • ∫ A, (βi A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA := by
      rw [hfr, hfi]
      exact congrArg₂ (fun s t => s + Complex.I • t) (hpart hr.continuous hrc hru)
        (hpart hi.continuous hic hiu)
    have e2 : ∫ A, (βr A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA +
          Complex.I • ∫ A, (βi A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA =
        ∫ A, (c : ℂ) • (((βr A : ℂ) + (βi A : ℂ) * Complex.I) • cuspRepT μ (archProj K n A) v) ∂νA :=
      (congrArg (fun s => ∫ A, (βr A : ℂ) • cuspRepT μ (archProj K n A) ((c : ℂ) • v) ∂νA + s)
        (integral_smul Complex.I _).symm).trans
        ((integral_add hIr (hIi.smul Complex.I)).symm.trans
          (integral_congr_ae (Eventually.of_forall hpt)))
    have e3 : ∫ A, (c : ℂ) • (((βr A : ℂ) + (βi A : ℂ) * Complex.I) • cuspRepT μ (archProj K n A) v) ∂νA =
        ∫ a, (c : ℂ) • (κ a • archRepT μ a v) ∂ν := by
      rw [hνA]
      refine (integral_map_val ν (fun A => (c : ℂ) • (((βr A : ℂ) + (βi A : ℂ) * Complex.I) •
        cuspRepT μ (archProj K n A) v))).trans ?_
      exact integral_congr_ae (Eventually.of_forall fun a =>
        congrArg (fun t => (c : ℂ) • (t • archRepT μ a v)) (hκβ a).symm)
    have e4 : ∫ a, (c : ℂ) • (κ a • archRepT μ a v) ∂ν = (c : ℂ) • v :=
      (integral_smul (c : ℂ) _).trans (congrArg (fun z => (c : ℂ) • z) hκv)
    exact e1.trans (e2.trans (e3.trans e4))
  have hrepr : IsContRep μ ((c : ℂ) • toLp μ v)
      (rconv Γ₁ μ fr (toLp μ v) + Complex.I • rconv Γ₁ μ fi (toLp μ v)) := by
    refine ((isContRep_rconv μ fr (toLp μ v)).add
      ((isContRep_rconv μ fi (toLp μ v)).smul Complex.I)).of_eq ?_
    refine (congrArg₂ (fun s t => s + Complex.I • t) (hsub fr) (hsub fi)).trans ?_
    refine ((congrArg (fun t => toLp μ ((cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fr) v) + t)
      ((toLp μ).map_smul Complex.I ((cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ fi) v)).symm).trans
      ((toLp μ).map_add _ _).symm).trans ?_
    exact (congrArg (toLp μ) hcomb).trans ((toLp μ).map_smul (c : ℂ) v)
  have hΦ2 : Φ = (c : ℂ)⁻¹ • (rconv Γ₁ μ fr (toLp μ v) + Complex.I • rconv Γ₁ μ fi (toLp μ v)) :=
    hrep.unique ((hrepr.smul (c : ℂ)⁻¹).of_eq (hcancel _))
  refine ⟨κ, U, Φ, ‖(c : ℂ)⁻¹‖ * (Br * ‖toLp μ v‖ + Bi * ‖toLp μ v‖), hκt, hκv, hU, hrep,
    fun y => ?_, ?_, ?_⟩
  · have h1 := hBr _ (toLp_mem μ v) y
    have h2 := hBi _ (toLp_mem μ v) y
    rw [← hfr] at h1
    rw [← hfi] at h2
    rw [hΦ2]
    show ‖(c : ℂ)⁻¹ • (rconv Γ₁ μ fr (toLp μ v) y + Complex.I • rconv Γ₁ μ fi (toLp μ v) y)‖ ≤ _
    rw [norm_smul]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 ?_)) (norm_nonneg _)
    rw [norm_smul, Complex.norm_I, one_mul]
    exact h2
  · intro u hu x
    rw [hΦ]
    simp only [Pi.smul_apply]
    congr 1
    refine rconv_mul_of_left_inv μ (fun z => ?_) _ x
    rw [← map_inv]
    exact hF₀U _ (U.inv_mem hu) z
  · intro r hr0 hrn x
    rw [hΦ]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_rconv_unip_eq_zero μ F₀ (toLp_mem μ v) hr0 hrn x, mul_zero]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
