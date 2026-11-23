import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsBase
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.IsHilbertSchmidtOfAeEqDual

open MeasureTheory Set Filter Topology Function
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open AutomorphicForm RightCosetSpace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => Reduction.rationalGLOne K n

def quotFun (F : normOneGL K n → ℂ) (hF : ∀ γ ∈ Γ₁, ∀ y, F (γ * y) = F y) :
    RightCosetSpace Γ₁ → ℂ :=
  Quotient.lift F fun a b hab => by
    obtain ⟨γ, rfl⟩ := hab
    exact hF γ γ.2 b

@[simp] theorem quotFun_mk (F : normOneGL K n → ℂ) (hF : ∀ γ ∈ Γ₁, ∀ y, F (γ * y) = F y)
    (y : normOneGL K n) : quotFun F hF (mk Γ₁ y) = F y := rfl

theorem continuous_quotFun {F : normOneGL K n → ℂ} (hF : ∀ γ ∈ Γ₁, ∀ y, F (γ * y) = F y)
    (hc : Continuous F) : Continuous (quotFun F hF) :=
  (isOpenQuotientMap_mk Γ₁).isQuotientMap.continuous_iff.2 hc

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def IsContRep (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (F : normOneGL K n → ℂ) : Prop :=
  Continuous F ∧ (∀ γ ∈ Γ₁, ∀ y, F (γ * y) = F y) ∧ (fun y => φ (mk Γ₁ y)) =ᵐ[μ] F

variable {μ}

theorem IsContRep.unique {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F F' : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) (h' : IsContRep μ φ F') : F = F' :=
  (h.1.ae_eq_iff_eq μ h'.1).1 (h.2.2.symm.trans h'.2.2)

theorem isContRep_zero : IsContRep μ (0 : Lp ℂ 2 (quotientMeasure Γ₁ μ)) 0 := by
  refine ⟨continuous_const, fun _ _ _ => rfl, ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp
    (Lp.coeFn_zero ℂ 2 (quotientMeasure Γ₁ μ))] with y hy
  exact hy

theorem IsContRep.add {φ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F F' : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) (h' : IsContRep μ ψ F') : IsContRep μ (φ + ψ) (F + F') := by
  refine ⟨h.1.add h'.1, fun γ hγ y => by simp [h.2.1 γ hγ y, h'.2.1 γ hγ y], ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (Lp.coeFn_add φ ψ), h.2.2, h'.2.2]
    with y h1 h2 h3
  simp only [Function.comp_apply, Pi.add_apply] at h1
  rw [h1, h2, h3, Pi.add_apply]

theorem IsContRep.smul (c : ℂ) {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) : IsContRep μ (c • φ) (c • F) := by
  refine ⟨h.1.const_smul c, fun γ hγ y => by simp [h.2.1 γ hγ y], ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (Lp.coeFn_smul c φ), h.2.2]
    with y h1 h2
  simp only [Function.comp_apply, Pi.smul_apply] at h1
  rw [h1, h2, Pi.smul_apply]

theorem IsContRep.translate {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) (x : normOneGL K n) :
    IsContRep μ (rightRegularRep Γ₁ μ x φ) (fun y => F (y * x)) := by
  refine ⟨h.1.comp (continuous_mul_const x), fun γ hγ y => by
    show F (γ * y * x) = F (y * x)
    rw [mul_assoc, h.2.1 γ hγ], ?_⟩
  have h2 : (fun y => φ (mk Γ₁ (y * x))) =ᵐ[μ] fun y => F (y * x) :=
    (measurePreserving_mul_right μ x).quasiMeasurePreserving.ae_eq_comp h.2.2
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (coeFn_rightRegularRep Γ₁ μ x φ), h2]
    with y hy1 hy2
  simp only [Function.comp_apply, rightMul_mk] at hy1
  rw [hy1]
  exact hy2

variable (μ) in

theorem isContRep_rconv (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    IsContRep μ ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) φ)
      (rconv Γ₁ μ f φ) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  refine ⟨continuous_rconv Γ₁ μ f φ, fun γ hγ y => rconv_mul_left Γ₁ μ f φ hγ y, ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (integrated_ae_eq_rconvQ Γ₁ μ f φ)]
    with y hy
  simp only [Function.comp_apply] at hy
  rw [hy, rconvQ_mk]

theorem IsContRep.ae_eq_quotFun {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : IsContRep μ φ F) :
    (φ : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] quotFun F h.2.1 := by
  have hm : ∀ᵐ x ∂(Measure.map (mk Γ₁) (μ.restrict (fundamentalDomain Γ₁))),
      (φ : RightCosetSpace Γ₁ → ℂ) x = quotFun F h.2.1 x := by
    refine (ae_map_iff (measurable_mk Γ₁).aemeasurable
      (measurableSet_eq_fun (Lp.stronglyMeasurable φ).measurable
        (continuous_quotFun h.2.1 h.1).measurable)).2 ?_
    exact ae_restrict_of_ae (h.2.2.mono fun y hy => by simpa using hy)
  rwa [map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain Γ₁ μ)] at hm

variable (μ)
variable (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]

theorem integrable_smul_archRep {γ : archGroup K n → ℂ} (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (w : cuspidalL2 μ) :
    Integrable (fun a => γ a • archRep μ a w) ν :=
  (hγ.smul ((archRep μ).continuous_orbit w)).integrable_of_hasCompactSupport hγc.smul_right

theorem coe_integrated_archRep {γ : archGroup K n → ℂ} (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (w : cuspidalL2 μ) :
    (((archRep μ).integrated ν γ w : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) =
      ∫ a, γ a • rightRegularRep Γ₁ μ (archP K n a) (w : Lp ℂ 2 (quotientMeasure Γ₁ μ)) ∂ν := by
  have e := (cuspidalL2 μ).subtypeL.integral_comp_comm (integrable_smul_archRep μ ν hγ hγc w)
  exact e.symm.trans (integral_congr_ae (Eventually.of_forall fun a => rfl))

set_option maxHeartbeats 1000000 in

theorem hasContRep_integrated_archRep {w : cuspidalL2 μ} {W : normOneGL K n → ℂ}
    (hW : IsContRep μ (w : Lp ℂ 2 (quotientMeasure Γ₁ μ)) W) {C : ℝ} (hWb : ∀ y, ‖W y‖ ≤ C)
    {γ : archGroup K n → ℂ} (hγ : Continuous γ) (hγc : HasCompactSupport γ) :
    IsContRep μ (((archRep μ).integrated ν γ w : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ))
      (fun y => ∫ a, γ a * W (y * archP K n a) ∂ν) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  obtain ⟨S, hS⟩ : ∃ S, S = tsupport γ := ⟨_, rfl⟩
  have hSc : IsCompact S := hS ▸ hγc.isCompact
  have hWc : Continuous W := hW.1
  have hpc : Continuous (archP K n) := continuous_archP

  have hJ : Continuous (uncurry fun (y : normOneGL K n) (a : archGroup K n) =>
      γ a * W (y * archP K n a)) :=
    (hγ.comp continuous_snd).mul (hWc.comp (continuous_fst.mul (hpc.comp continuous_snd)))
  have hset : ∀ y, ∫ a, γ a * W (y * archP K n a) ∂ν = ∫ a in S, γ a * W (y * archP K n a) ∂ν := by
    intro y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => ?_).symm
    have h0 : γ a = 0 := image_eq_zero_of_notMem_tsupport (by rw [← hS]; exact ha)
    rw [h0, zero_mul]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : normOneGL K n → ℂ, Ψ = fun y => ∫ a, γ a * W (y * archP K n a) ∂ν :=
    ⟨_, rfl⟩
  have hΨc : Continuous Ψ := by
    have : Ψ = fun y => ∫ a in S, γ a * W (y * archP K n a) ∂ν := hΨ.trans (funext hset)
    rw [this]
    exact continuous_parametric_integral_of_continuous hJ hSc
  have hΨinv : ∀ γ₀ ∈ Γ₁, ∀ y, Ψ (γ₀ * y) = Ψ y := by
    intro γ₀ hγ₀ y
    rw [hΨ]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    show γ a * W (γ₀ * y * archP K n a) = γ a * W (y * archP K n a)
    rw [mul_assoc, hW.2.1 γ₀ hγ₀]
  rw [← hΨ]
  refine ⟨hΨc, hΨinv, ?_⟩

  obtain ⟨WQ, hWQ⟩ : ∃ WQ, WQ = quotFun W hW.2.1 := ⟨_, rfl⟩
  have hWQc : Continuous WQ := hWQ ▸ continuous_quotFun hW.2.1 hWc
  have hWQb : ∀ x, ‖WQ x‖ ≤ C := by
    intro x
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ x
    rw [hWQ, quotFun_mk]
    exact hWb y
  obtain ⟨ΨQ, hΨQ⟩ : ∃ ΨQ, ΨQ = quotFun Ψ hΨinv := ⟨_, rfl⟩
  have hΨQ_eq : ∀ x, ΨQ x = ∫ a, γ a * WQ (rightMul Γ₁ (archP K n a) x) ∂ν := by
    intro x
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ x
    rw [hΨQ, quotFun_mk, hΨ, hWQ]
    simp only [rightMul_mk, quotFun_mk]
  have hγi : Integrable γ ν := hγ.integrable_of_hasCompactSupport hγc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hWb 1)

  have hJQ : Continuous (uncurry fun (a : archGroup K n) (x : RightCosetSpace Γ₁) =>
      γ a * WQ (rightMul Γ₁ (archP K n a) x)) := by
    have hr : Continuous fun p : archGroup K n × RightCosetSpace Γ₁ =>
        rightMul Γ₁ (archP K n p.1) p.2 := by
      have h1 : Continuous fun p : RightCosetSpace Γ₁ × normOneGL K n => rightMul Γ₁ p.2 p.1 :=
        continuous_rightMul_prod Γ₁
      have h2 : Continuous fun p : archGroup K n × RightCosetSpace Γ₁ => (p.2, archP K n p.1) :=
        continuous_snd.prodMk (hpc.comp continuous_fst)
      have h3 := h1.comp h2
      exact h3
    have h4 := (hγ.comp continuous_fst).mul (hWQc.comp hr)
    exact h4
  have hint : ∀ s : Set (RightCosetSpace Γ₁), Integrable (uncurry fun (a : archGroup K n)
      (x : RightCosetSpace Γ₁) => γ a * WQ (rightMul Γ₁ (archP K n a) x))
        (ν.prod ((quotientMeasure Γ₁ μ).restrict s)) := by
    intro s
    refine Integrable.mono' ((hγi.norm.mul_prod (integrable_const C))) hJQ.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    obtain ⟨a, x⟩ := p
    show ‖γ a * WQ (rightMul Γ₁ (archP K n a) x)‖ ≤ ‖γ a‖ * C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hWQb _) (norm_nonneg _)
  have hΨQi : Integrable ΨQ (quotientMeasure Γ₁ μ) := by
    have := (hint univ).integral_prod_right
    rw [Measure.restrict_univ] at this
    exact this.congr (Eventually.of_forall fun x => (hΨQ_eq x).symm)

  obtain ⟨V, hV⟩ : ∃ V : Lp ℂ 2 (quotientMeasure Γ₁ μ),
      V = ∫ a, γ a • rightRegularRep Γ₁ μ (archP K n a) (w : Lp ℂ 2 (quotientMeasure Γ₁ μ)) ∂ν :=
    ⟨_, rfl⟩
  have hVi : Integrable (fun a => γ a • rightRegularRep Γ₁ μ (archP K n a)
      (w : Lp ℂ 2 (quotientMeasure Γ₁ μ))) ν :=
    (hγ.smul (((rightRegularRep Γ₁ μ).continuous_orbit _).comp hpc)).integrable_of_hasCompactSupport
      hγc.smul_right
  have hwQ : (w : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] WQ := hWQ ▸ hW.ae_eq_quotFun
  have hVeq : (V : RightCosetSpace Γ₁ → ℂ) =ᵐ[quotientMeasure Γ₁ μ] ΨQ := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s _ _ => ((Lp.memLp _).integrable one_le_two).integrableOn)
      (fun s _ _ => hΨQi.integrableOn) fun s hs hμs => ?_
    rw [← L2.inner_indicatorConstLp_one hs hμs.ne, hV, ← integral_inner hVi]
    have hcoef : ∀ a, ⟪indicatorConstLp 2 hs hμs.ne (1 : ℂ), γ a • rightRegularRep Γ₁ μ
        (archP K n a) (w : Lp ℂ 2 (quotientMeasure Γ₁ μ))⟫_ℂ =
        ∫ x in s, γ a * WQ (rightMul Γ₁ (archP K n a) x) ∂quotientMeasure Γ₁ μ := by
      intro a
      rw [inner_smul_right, L2.inner_indicatorConstLp_one, ← integral_const_mul]
      refine setIntegral_congr_ae hs ?_
      have h1 := coeFn_rightRegularRep Γ₁ μ (archP K n a) (w : Lp ℂ 2 (quotientMeasure Γ₁ μ))
      have h2 := (measurePreserving_rightMul μ (archP K n a)).quasiMeasurePreserving.ae_eq_comp hwQ
      filter_upwards [h1, h2] with x hx1 hx2
      intro _
      simp only [Function.comp_apply] at hx2
      exact congrArg (γ a * ·) (hx1.trans hx2)
    simp_rw [hcoef]
    refine (integral_integral_swap (hint s)).trans ?_
    exact setIntegral_congr_fun hs fun x _ => (hΨQ_eq x).symm
  have hcoe := (coe_integrated_archRep μ ν hγ hγc w).trans hV.symm
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp hVeq] with y hy
  simp only [Function.comp_apply] at hy
  refine (congrArg (fun f : Lp ℂ 2 (quotientMeasure Γ₁ μ) =>
    (f : RightCosetSpace Γ₁ → ℂ) (mk Γ₁ y)) hcoe).trans ?_
  refine hy.trans ?_
  rw [hΨQ, quotFun_mk]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
