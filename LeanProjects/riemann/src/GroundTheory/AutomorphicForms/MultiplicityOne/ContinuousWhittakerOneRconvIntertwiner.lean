import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.Functional

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep (normOneGL K n) H}

variable (μ σ) in

def cuspIntertwiners : Submodule ℂ (H →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ)) where
  carrier := {T | T ∈ σ.intertwiners (rightRegularRep Γ₁ μ) ∧ ∀ v, T v ∈ cuspidalL2 μ}
  add_mem' hS hT := ⟨add_mem hS.1 hT.1, fun v => add_mem (hS.2 v) (hT.2 v)⟩
  zero_mem' := ⟨zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ hT := ⟨Submodule.smul_mem _ c hT.1, fun v => Submodule.smul_mem _ c (hT.2 v)⟩

theorem cuspIntertwiners_map (T : cuspIntertwiners μ σ) (x : normOneGL K n) (w : H) :
    T.1 (σ x w) = rightRegularRep Γ₁ μ x (T.1 w) :=
  T.2.1 x w

theorem cuspIntertwiners_integrated (T : cuspIntertwiners μ σ)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (v : H) :
    T.1 (σ.integrated μ (UnitaryRep.ccToL1 μ f) v) =
      (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) (T.1 v) :=
  congrArg (fun L : H →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ) => L v)
    (UnitaryRep.comp_integrated_of_mem_intertwiners σ μ T.2.1 (UnitaryRep.ccToL1 μ f))

theorem hasContRep_intertwiner_integrated (T : cuspIntertwiners μ σ)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (v : H) :
    HasContRep μ (T.1 (σ.integrated μ (UnitaryRep.ccToL1 μ f) v)) (rconv Γ₁ μ f (T.1 v)) :=
  Eq.subst (motive := fun φ => HasContRep μ φ (rconv Γ₁ μ f (T.1 v)))
    (cuspIntertwiners_integrated T f v).symm (hasContRep_rconv μ f (T.1 v))

theorem hasContRep_intertwiner_generator (T : cuspIntertwiners μ σ) (x : normOneGL K n)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (v : H) :
    HasContRep μ (T.1 (σ x (σ.integrated μ (UnitaryRep.ccToL1 μ f) v)))
      (fun y => rconv Γ₁ μ f (T.1 v) (y * x)) :=
  Eq.subst (motive := fun φ => HasContRep μ φ (fun y => rconv Γ₁ μ f (T.1 v) (y * x)))
    (cuspIntertwiners_map T x _).symm ((hasContRep_intertwiner_integrated T f v).translate x)

theorem exists_hasContRep (T : cuspIntertwiners μ σ) {w : H} (hw : w ∈ smoothSpan μ σ) :
    ∃ F, HasContRep μ (T.1 w) F := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, f, v, -, rfl⟩ := hw
    exact ⟨_, hasContRep_intertwiner_generator T x f v⟩
  | zero =>
    exact ⟨0, Eq.subst (motive := fun φ => HasContRep μ φ 0) (map_zero T.1).symm hasContRep_zero⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨F₁, h₁⟩ := h₁
    obtain ⟨F₂, h₂⟩ := h₂
    exact ⟨F₁ + F₂, Eq.subst (motive := fun φ => HasContRep μ φ (F₁ + F₂))
      (map_add T.1 w₁ w₂).symm (h₁.add h₂)⟩
  | smul c w _ h =>
    obtain ⟨F, h⟩ := h
    exact ⟨c • F, Eq.subst (motive := fun φ => HasContRep μ φ (c • F))
      (map_smul T.1 c w).symm (h.smul c)⟩

open Classical in
variable (μ σ) in

def whittakerAt (T : cuspIntertwiners μ σ) (w : H) : ℂ :=
  if h : ∃ F, HasContRep μ (T.1 w) F then whittakerOne h.choose 1 else 0

theorem whittakerAt_eq {T : cuspIntertwiners μ σ} {w : H} {F : normOneGL K n → ℂ}
    (h : HasContRep μ (T.1 w) F) : whittakerAt μ σ T w = whittakerOne F 1 := by
  have hex : ∃ F, HasContRep μ (T.1 w) F := ⟨F, h⟩
  rw [whittakerAt, dif_pos hex, hex.choose_spec.unique h]

def whittakerOf (T : cuspIntertwiners μ σ) : Module.Dual ℂ (smoothSpan μ σ) where
  toFun w := whittakerAt μ σ T w
  map_add' w₁ w₂ := by
    obtain ⟨F₁, h₁⟩ := exists_hasContRep T w₁.2
    obtain ⟨F₂, h₂⟩ := exists_hasContRep T w₂.2
    have h : HasContRep μ (T.1 ((w₁ + w₂ : smoothSpan μ σ) : H)) (F₁ + F₂) :=
      Eq.subst (motive := fun φ => HasContRep μ φ (F₁ + F₂))
        (map_add T.1 (w₁ : H) (w₂ : H)).symm (h₁.add h₂)
    rw [whittakerAt_eq h, whittakerAt_eq h₁, whittakerAt_eq h₂, whittakerOne_add h₁.1 h₂.1]
  map_smul' c w := by
    obtain ⟨F, h₁⟩ := exists_hasContRep T w.2
    have h : HasContRep μ (T.1 ((c • w : smoothSpan μ σ) : H)) (c • F) :=
      Eq.subst (motive := fun φ => HasContRep μ φ (c • F)) (map_smul T.1 c (w : H)).symm (h₁.smul c)
    rw [whittakerAt_eq h, whittakerAt_eq h₁, whittakerOne_smul, RingHom.id_apply, smul_eq_mul]

theorem whittakerOf_apply (T : cuspIntertwiners μ σ) (w : smoothSpan μ σ) :
    whittakerOf T w = whittakerAt μ σ T w := rfl

theorem whittakerOf_mk (T : cuspIntertwiners μ σ) {a : H} (ha : a ∈ smoothSpan μ σ)
    {F : normOneGL K n → ℂ} (h : HasContRep μ (T.1 a) F) :
    whittakerOf T ⟨a, ha⟩ = whittakerOne F 1 :=
  whittakerAt_eq h

theorem whittakerOf_generator (T : cuspIntertwiners μ σ) (x : normOneGL K n)
    {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ} (hf : IsSmoothTest f) (v : H) :
    whittakerOf T ⟨σ x (σ.integrated μ (UnitaryRep.ccToL1 μ f) v),
        map_mem_smoothSpan σ x (integrated_mem_smoothSpan σ hf v)⟩ =
      whittakerOne (rconv Γ₁ μ f (T.1 v)) x := by
  refine (whittakerOf_mk T _ (hasContRep_intertwiner_generator T x f v)).trans ?_
  exact (whittakerOne_mul_right _ 1 x).trans (congrArg _ (one_mul x))

set_option maxHeartbeats 1000000 in

theorem continuous_whittakerOne_rconv_intertwiner (T : cuspIntertwiners μ σ)
    {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ} (hf : IsSmoothTest f) :
    Continuous fun v : H => whittakerOne (rconv Γ₁ μ f (T.1 v)) 1 := by
  obtain ⟨ν, hν, U, hU, β, hβ, hβc, hβu, g, rfl⟩ := hf
  obtain ⟨B, hB⟩ := exists_norm_rconv_le_uniform μ ν hβ hβc hβu U hU g
  let L : H →ₗ[ℂ] ℂ :=
    { toFun := fun v => whittakerOne (rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g))
        (T.1 v)) 1
      map_add' := fun v v' => by
        have e : rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) (T.1 (v + v')) =
            rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) (T.1 v) +
              rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) (T.1 v') := by
          funext y
          exact (congrArg (fun φ => rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) φ y)
            (map_add T.1 v v')).trans (rconv_add Γ₁ μ _ _ _ y)
        exact (congrArg (fun F => whittakerOne F 1) e).trans
          (whittakerOne_add (continuous_rconv Γ₁ μ _ _) (continuous_rconv Γ₁ μ _ _) 1)
      map_smul' := fun c v => by
        have e : rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) (T.1 (c • v)) =
            c • rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) (T.1 v) := by
          funext y
          exact (congrArg (fun φ => rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) φ y)
            (map_smul T.1 c v)).trans (rconv_smul Γ₁ μ _ _ _ y)
        exact (congrArg (fun F => whittakerOne F 1) e).trans (whittakerOne_smul c _ 1) }
  refine AddMonoidHomClass.continuous_of_bound L (max B 0 * ‖T.1‖) fun v => ?_
  calc ‖L v‖ ≤ B * ‖T.1 v‖ := norm_whittakerOne_le (fun y => hB _ (T.2.2 v) y) 1
    _ ≤ max B 0 * ‖T.1 v‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max B 0 * (‖T.1‖ * ‖v‖) := mul_le_mul_of_nonneg_left (T.1.le_opNorm v) (le_max_right _ _)
    _ = max B 0 * ‖T.1‖ * ‖v‖ := (mul_assoc _ _ _).symm

theorem whittakerOf_mem (T : cuspIntertwiners μ σ) : whittakerOf T ∈ whittakerFunctionals μ σ := by
  refine ⟨fun X w => ?_, fun f hf => ?_⟩
  · obtain ⟨F, hF⟩ := exists_hasContRep T w.2
    have h : HasContRep μ (T.1 (σ (uOne X) w)) (fun y => F (y * uOne X)) :=
      Eq.subst (motive := fun φ => HasContRep μ φ (fun y => F (y * uOne X)))
        (cuspIntertwiners_map T (uOne X) w).symm (hF.translate (uOne X))
    have h1 : (1 : normOneGL K n) * uOne X = uOne X * 1 := (one_mul _).trans (mul_one _).symm
    refine (whittakerOf_mk T _ h).trans ?_
    refine (whittakerOne_mul_right _ 1 (uOne X)).trans ((congrArg _ h1).trans
      ((whittakerOne_uOne_mul hF.1 hF.2.1 X 1).trans ?_))
    exact congrArg _ (whittakerAt_eq hF).symm
  · have e : ∀ v : H, whittakerOf T ⟨σ.integrated μ (UnitaryRep.ccToL1 μ f) v,
        integrated_mem_smoothSpan σ hf v⟩ = whittakerOne (rconv Γ₁ μ f (T.1 v)) 1 :=
      fun v => whittakerOf_mk T _ (hasContRep_intertwiner_integrated T f v)
    exact (continuous_whittakerOne_rconv_intertwiner T hf).congr fun v => (e v).symm

set_option maxHeartbeats 1000000 in

theorem eq_zero_of_whittakerOf_eq_zero (T : cuspIntertwiners μ σ) (h : whittakerOf T = 0) :
    T = 0 := by
  have key : ∀ v, T.1 v = 0 := by
    intro v
    refine eq_zero_of_forall_whittakerOne_rconv_eq_zero μ (T.2.2 v) fun f hf x => ?_
    have e := whittakerOf_generator T x hf v
    have e2 := LinearMap.congr_fun h ⟨σ x (σ.integrated μ (UnitaryRep.ccToL1 μ f) v),
      map_mem_smoothSpan σ x (integrated_mem_smoothSpan σ hf v)⟩
    exact e.symm.trans e2
  exact Subtype.ext (ContinuousLinearMap.ext key)

theorem whittakerAt_add (T₁ T₂ : cuspIntertwiners μ σ) {w : H} {F₁ F₂ : normOneGL K n → ℂ}
    (h₁ : HasContRep μ (T₁.1 w) F₁) (h₂ : HasContRep μ (T₂.1 w) F₂) :
    whittakerAt μ σ (T₁ + T₂) w = whittakerAt μ σ T₁ w + whittakerAt μ σ T₂ w := by
  have h : HasContRep μ ((T₁ + T₂).1 w) (F₁ + F₂) := by
    rw [Submodule.coe_add, add_apply]
    exact h₁.add h₂
  rw [whittakerAt_eq h, whittakerAt_eq h₁, whittakerAt_eq h₂, whittakerOne_add h₁.1 h₂.1]

theorem whittakerAt_smul (c : ℂ) (T₁ : cuspIntertwiners μ σ) {w : H} {F₁ : normOneGL K n → ℂ}
    (h₁ : HasContRep μ (T₁.1 w) F₁) :
    whittakerAt μ σ (c • T₁) w = c * whittakerAt μ σ T₁ w := by
  have h : HasContRep μ ((c • T₁).1 w) (c • F₁) := by
    rw [Submodule.coe_smul, smul_apply]
    exact h₁.smul c
  rw [whittakerAt_eq h, whittakerAt_eq h₁, whittakerOne_smul]

set_option maxHeartbeats 2000000 in
theorem whittakerAt_add' (T₁ T₂ : cuspIntertwiners μ σ) {w : H} (hw : w ∈ smoothSpan μ σ) :
    whittakerAt μ σ (T₁ + T₂) w = whittakerAt μ σ T₁ w + whittakerAt μ σ T₂ w := by
  obtain ⟨F₁, h₁⟩ := exists_hasContRep T₁ hw
  obtain ⟨F₂, h₂⟩ := exists_hasContRep T₂ hw
  exact whittakerAt_add T₁ T₂ h₁ h₂

set_option maxHeartbeats 2000000 in
theorem whittakerAt_smul' (c : ℂ) (T₁ : cuspIntertwiners μ σ) {w : H} (hw : w ∈ smoothSpan μ σ) :
    whittakerAt μ σ (c • T₁) w = c * whittakerAt μ σ T₁ w := by
  obtain ⟨F₁, h₁⟩ := exists_hasContRep T₁ hw
  exact whittakerAt_smul c T₁ h₁

theorem whittakerOf_add (T₁ T₂ : cuspIntertwiners μ σ) :
    whittakerOf (T₁ + T₂ : cuspIntertwiners μ σ) = whittakerOf T₁ + whittakerOf T₂ :=
  LinearMap.ext fun w => whittakerAt_add' T₁ T₂ w.2

theorem whittakerOf_smul (c : ℂ) (T₁ : cuspIntertwiners μ σ) :
    whittakerOf (c • T₁ : cuspIntertwiners μ σ) = c • whittakerOf T₁ :=
  LinearMap.ext fun w => whittakerAt_smul' c T₁ w.2

variable (μ σ) in

def whittakerMap : cuspIntertwiners μ σ →ₗ[ℂ] whittakerFunctionals μ σ where
  toFun T := ⟨whittakerOf T, whittakerOf_mem T⟩
  map_add' T₁ T₂ := Subtype.ext (whittakerOf_add T₁ T₂)
  map_smul' c T₁ := Subtype.ext (whittakerOf_smul c T₁)

theorem whittakerMap_injective : Function.Injective (whittakerMap μ σ) := by
  refine (injective_iff_map_eq_zero _).2 fun T hT => ?_
  exact eq_zero_of_whittakerOf_eq_zero T (congrArg Subtype.val hT)

set_option maxHeartbeats 2000000 in
variable (μ σ) in

theorem rank_cuspIntertwiners_le_one (h : Module.rank ℂ (whittakerFunctionals μ σ) ≤ 1) :
    Module.rank ℂ (cuspIntertwiners μ σ) ≤ 1 := by
  have h1 := LinearMap.lift_rank_le_of_injective (whittakerMap μ σ) whittakerMap_injective
  exact Cardinal.lift_le_one_iff.1 (h1.trans (Cardinal.lift_le_one_iff.2 h))

end MultiplicityOne

end

end GroundTheory.Automorphic
