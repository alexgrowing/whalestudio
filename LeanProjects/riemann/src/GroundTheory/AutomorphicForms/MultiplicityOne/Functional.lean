import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

theorem whittakerOne_eq_whittaker_lift (ϕ : normOneGL K n → ℂ) (x : normOneGL K n) :
    whittakerOne ϕ x = whittaker (lift ϕ) (x : AdelicGLn.AdelicGL K n) := by
  rw [whittaker_lift, retract_coe]

theorem whittakerOne_uOne_mul {ϕ : normOneGL K n → ℂ} (hc : Continuous ϕ)
    (hl : ∀ γ ∈ Γ₁, ∀ y, ϕ (γ * y) = ϕ y) (X : Pos n → 𝔸[K]) (x : normOneGL K n) :
    whittakerOne ϕ (uOne X * x) =
      (GroundTheory.Global.adelicChar K (supSum 0 X) : ℂ) * whittakerOne ϕ x := by
  rw [whittakerOne_eq_whittaker_lift, whittakerOne_eq_whittaker_lift, Subgroup.coe_mul, coe_uOne]
  exact whittaker_uGL_mul (continuous_lift hc) (isLeftInvariant_lift hl) X x

theorem whittakerOne_mul_right (ϕ : normOneGL K n → ℂ) (x y : normOneGL K n) :
    whittakerOne (fun z => ϕ (z * y)) x = whittakerOne ϕ (x * y) := by
  unfold whittakerOne
  simp_rw [mul_assoc]

theorem continuous_uOne : Continuous (uOne (K := K) (n := n)) :=
  continuous_induced_rng.2 continuous_uGL

theorem continuous_adelicChar_neg_supSum :
    Continuous fun X : Pos n → 𝔸[K] => (GroundTheory.Global.adelicChar K (-supSum 0 X) : ℂ) :=
  continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)

theorem integrableOn_whittakerOne {ϕ : normOneGL K n → ℂ} (hc : Continuous ϕ) (x : normOneGL K n) :
    IntegrableOn (fun X => ϕ (uOne X * x) * (GroundTheory.Global.adelicChar K (-supSum 0 X) : ℂ))
      (vecDomain K (Pos n)) (vecMeasure K (Pos n)) := by
  have hcont : Continuous fun X : Pos n → 𝔸[K] =>
      ϕ (uOne X * x) * (GroundTheory.Global.adelicChar K (-supSum 0 X) : ℂ) :=
    (hc.comp (continuous_uOne.mul continuous_const)).mul continuous_adelicChar_neg_supSum
  exact (hcont.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure

theorem whittakerOne_add {ϕ ϕ' : normOneGL K n → ℂ} (hc : Continuous ϕ) (hc' : Continuous ϕ')
    (x : normOneGL K n) : whittakerOne (ϕ + ϕ') x = whittakerOne ϕ x + whittakerOne ϕ' x := by
  unfold whittakerOne
  rw [← integral_add (integrableOn_whittakerOne hc x) (integrableOn_whittakerOne hc' x)]
  congr 1
  funext X
  simp only [Pi.add_apply, add_mul]

theorem whittakerOne_smul (c : ℂ) (ϕ : normOneGL K n → ℂ) (x : normOneGL K n) :
    whittakerOne (c • ϕ) x = c * whittakerOne ϕ x := by
  unfold whittakerOne
  rw [← integral_const_mul]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem whittakerOne_zero (x : normOneGL K n) : whittakerOne (0 : normOneGL K n → ℂ) x = 0 := by
  simp [whittakerOne]

theorem norm_whittakerOne_le {ϕ : normOneGL K n → ℂ} {B : ℝ} (hB : ∀ y, ‖ϕ y‖ ≤ B)
    (x : normOneGL K n) : ‖whittakerOne ϕ x‖ ≤ B := by
  unfold whittakerOne
  have h := norm_setIntegral_le_of_norm_le_const (μ := vecMeasure K (Pos n))
    (s := vecDomain K (Pos n)) (C := B)
    (f := fun X => ϕ (uOne X * x) * (GroundTheory.Global.adelicChar K (-supSum 0 X) : ℂ))
    (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top) fun X _ => by
      rw [norm_mul, Circle.norm_coe, mul_one]; exact hB _
  rwa [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one] at h

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

def HasContRep (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (F : normOneGL K n → ℂ) : Prop :=
  Continuous F ∧ (∀ γ ∈ Γ₁, ∀ y, F (γ * y) = F y) ∧ (fun y => φ (mk Γ₁ y)) =ᵐ[μ] F

variable {μ}

theorem HasContRep.unique {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F F' : normOneGL K n → ℂ}
    (h : HasContRep μ φ F) (h' : HasContRep μ φ F') : F = F' :=
  (h.1.ae_eq_iff_eq μ h'.1).1 (h.2.2.symm.trans h'.2.2)

theorem hasContRep_zero : HasContRep μ (0 : Lp ℂ 2 (quotientMeasure Γ₁ μ)) 0 := by
  refine ⟨continuous_const, fun _ _ _ => rfl, ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp
    (Lp.coeFn_zero ℂ 2 (quotientMeasure Γ₁ μ))] with y hy
  exact hy

theorem HasContRep.add {φ ψ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F F' : normOneGL K n → ℂ}
    (h : HasContRep μ φ F) (h' : HasContRep μ ψ F') : HasContRep μ (φ + ψ) (F + F') := by
  refine ⟨h.1.add h'.1, fun γ hγ y => by simp [h.2.1 γ hγ y, h'.2.1 γ hγ y], ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (Lp.coeFn_add φ ψ), h.2.2, h'.2.2]
    with y h1 h2 h3
  simp only [Function.comp_apply, Pi.add_apply] at h1
  rw [h1, h2, h3, Pi.add_apply]

theorem HasContRep.smul (c : ℂ) {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : HasContRep μ φ F) : HasContRep μ (c • φ) (c • F) := by
  refine ⟨h.1.const_smul c, fun γ hγ y => by simp [h.2.1 γ hγ y], ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (Lp.coeFn_smul c φ), h.2.2]
    with y h1 h2
  simp only [Function.comp_apply, Pi.smul_apply] at h1
  rw [h1, h2, Pi.smul_apply]

variable (μ) in

theorem hasContRep_rconv (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) :
    HasContRep μ ((rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) φ)
      (rconv Γ₁ μ f φ) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  refine ⟨continuous_rconv Γ₁ μ f φ, fun γ hγ y => rconv_mul_left Γ₁ μ f φ hγ y, ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (integrated_ae_eq_rconvQ Γ₁ μ f φ)]
    with y hy
  simp only [Function.comp_apply] at hy
  rw [hy, rconvQ_mk]

theorem HasContRep.translate {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} {F : normOneGL K n → ℂ}
    (h : HasContRep μ φ F) (x : normOneGL K n) :
    HasContRep μ (rightRegularRep Γ₁ μ x φ) (fun y => F (y * x)) := by
  refine ⟨h.1.comp (continuous_mul_const x), fun γ hγ y => by
    show F (γ * y * x) = F (y * x)
    rw [mul_assoc, h.2.1 γ hγ], ?_⟩
  have h2 : (fun y => φ (mk Γ₁ (y * x))) =ᵐ[μ] fun y => F (y * x) :=
    (measurePreserving_mul_right μ x).quasiMeasurePreserving.ae_eq_comp h.2.2
  filter_upwards [(quasiMeasurePreserving_mk Γ₁ μ).ae_eq_comp (coeFn_rightRegularRep Γ₁ μ x φ), h2]
    with y h1 h3
  simp only [Function.comp_apply] at h1
  rw [h1, rightMul_mk, h3]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ) in

def smoothSpan (σ : UnitaryRep (normOneGL K n) H) : Submodule ℂ H :=
  Submodule.span ℂ {w | ∃ (x : normOneGL K n) (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    (v : H), IsSmoothTest f ∧ w = σ x (σ.integrated μ (UnitaryRep.ccToL1 μ f) v)}

theorem map_mem_smoothSpan (σ : UnitaryRep (normOneGL K n) H) (x : normOneGL K n) {w : H}
    (hw : w ∈ smoothSpan μ σ) : σ x w ∈ smoothSpan μ σ := by
  have : smoothSpan μ σ ≤ (smoothSpan μ σ).comap ((σ x : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, f, v, hf, rfl⟩
    refine Submodule.subset_span ⟨x * y, f, v, hf, ?_⟩
    rw [σ.map_mul_apply]
    rfl
  exact this hw

theorem integrated_mem_smoothSpan (σ : UnitaryRep (normOneGL K n) H)
    {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ} (hf : IsSmoothTest f) (v : H) :
    σ.integrated μ (UnitaryRep.ccToL1 μ f) v ∈ smoothSpan μ σ :=
  Submodule.subset_span ⟨1, f, v, hf, by rw [σ.map_one_apply]⟩

variable (μ) in

def whittakerFunctionals (σ : UnitaryRep (normOneGL K n) H) :
    Submodule ℂ (Module.Dual ℂ (smoothSpan μ σ)) where
  carrier := {Λ | (∀ (X : Pos n → 𝔸[K]) (w : smoothSpan μ σ),
      Λ ⟨σ (uOne X) w, map_mem_smoothSpan σ _ w.2⟩ =
        (GroundTheory.Global.adelicChar K (supSum 0 X) : ℂ) * Λ w) ∧
    ∀ f, ∀ hf : IsSmoothTest f,
      Continuous fun v : H => Λ ⟨σ.integrated μ (UnitaryRep.ccToL1 μ f) v,
        integrated_mem_smoothSpan σ hf v⟩}
  zero_mem' := ⟨fun X w => by simp, fun f hf => continuous_const⟩
  add_mem' {a b} ha hb := ⟨fun X w => by
      simp only [LinearMap.add_apply, ha.1 X w, hb.1 X w, mul_add],
    fun f hf => (ha.2 f hf).add (hb.2 f hf)⟩
  smul_mem' c a ha := ⟨fun X w => by
      simp only [LinearMap.smul_apply, ha.1 X w, smul_eq_mul]; ring,
    fun f hf => (ha.2 f hf).const_smul c⟩

end MultiplicityOne

end

end GroundTheory.Automorphic
