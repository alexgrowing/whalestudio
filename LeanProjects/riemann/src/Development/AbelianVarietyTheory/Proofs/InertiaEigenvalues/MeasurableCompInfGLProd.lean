import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousColConvIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.MspanROrth

open GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {ω : HChar E}

theorem measurable_chart_prod {F : GA E a → ℂ} (hF : Continuous F) :
    Measurable fun p : GA E a × Lie E a => chart F p.1 p.2 := by
  classical
  have h1 := GlobalTheory.ConstTermSmooth.continuousOn_chart (E := E) (a := a) hF
  have e : (fun p : GA E a × Lie E a => chart F p.1 p.2) =
      (Set.univ ×ˢ invSet E a).piecewise (fun p : GA E a × Lie E a => chart F p.1 p.2) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a))
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      exact dif_neg fun h => hp ⟨Set.mem_univ _, h⟩
  rw [e]
  exact h1.measurable_piecewise continuousOn_const (isOpen_univ.prod isOpen_invSet).measurableSet

theorem measurable_comp_infGL_prod {F : GA E a → ℂ} (hF : Continuous F) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun p : GA E a × X => F (p.1 * infGL E a (γ p.2)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun p : GA E a × X => F (p.1 * infGL E a (γ p.2))) =
      (fun q : GA E a × Lie E a => chart F q.1 q.2) ∘ fun p : GA E a × X => (p.1, toL (γ p.2).val) :=
    funext fun p => (chart_val F p.1 (γ p.2)).symm
  rw [e]
  exact (measurable_chart_prod hF).comp (measurable_fst.prodMk (h.comp measurable_snd))

theorem measurable_comp_infGL' {F : GA E a → ℂ} (hF : Continuous F) (g : GA E a) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun x => F (g * infGL E a (γ x)) :=
  by
  have h := (measurable_comp_infGL_prod hF hγ).comp (measurable_prodMk_left (x := g) (β := X))
  exact h

theorem integrable_of_isRapidInf {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) : Integrable k ν := by
  have h := hk.2.2 0
  simp only [pow_zero, mul_one] at h
  exact (integrable_norm_iff hk.1.aestronglyMeasurable).1 h

theorem kerInf_mem_bddForms {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {F : GA E a → ℂ} (h : F ∈ bddForms E a ω) :
    (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ∈ bddForms E a ω := by
  obtain ⟨C, hC⟩ := h.2.2.2
  have hki := integrable_of_isRapidInf hk
  refine ⟨?_, fun γ' g => ?_, fun z g => ?_, ∫ x, ‖k x‖ * C ∂ν, fun g => ?_⟩
  · refine continuous_of_dominated (bound := fun x => ‖k x‖ * C)
      (fun g => (hk.1.mul (measurable_comp_infGL' h.1 g hk.2.1)).aestronglyMeasurable)
      (fun g => .of_forall fun x => ?_) (hki.norm.mul_const C)
      (.of_forall fun x => continuous_const.mul (h.1.comp (continuous_id.mul continuous_const)))
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · simp only [mul_assoc, h.2.1]
  · rw [← integral_const_mul]
    beta_reduce
    congr 1; funext x; rw [mul_assoc, h.2.2.1]; ring
  · exact norm_integral_le_of_norm_le (hki.norm.mul_const C)
      (.of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))

section Lemmas

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem pet_kerInf_left (hω : ω.IsUnitary) {X : Type} [MeasurableSpace X] {ν : Measure X} [SFinite ν] {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {F ψ : GA E a → ℂ}
    (h : F ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) :
    pet (latticeGL E a) μ (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ψ =
      ∫ x, k x * pet (latticeGL E a) μ (fun g => F (g * infGL E a (γ x))) ψ ∂ν := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hD := isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI : IsFiniteMeasure (μ.restrict (stdDom (latticeGL E a))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ hD]; exact measure_lt_top _ _⟩
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD'⟩ := h'.2.2.2
  have hki := integrable_of_isRapidInf hk
  have hm : Measurable fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1) :=
    ((hk.1.comp measurable_snd).mul (measurable_comp_infGL_prod h.1 hk.2.1)).mul
      ((Complex.continuous_conj.comp h'.1).measurable.comp measurable_fst)
  have hi : Integrable (fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1))
      ((μ.restrict (stdDom (latticeGL E a))).prod ν) := by
    refine ((integrable_const (C * D)).mul_prod hki.norm).mono' hm.aestronglyMeasurable
      (.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD' _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC 1))) (norm_nonneg _)
  rw [(pet_eq_setIntegral hω (kerInf_mem_bddForms hk h) h' hD).2]
  simp only [← integral_mul_const]
  rw [integral_integral_swap hi]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [(pet_eq_setIntegral hω (mul_right_mem_bddForms h _) h' hD).2, ← integral_const_mul, mul_assoc]

theorem mul_right_mem_mspanR {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) (h : GA E a) :
    (fun g => F (g * h)) ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem mspanR_pet_eq_zero (hω : ω.IsUnitary) {π : CuspSub E a} (hπ : π.HasCentChar ω) (T : Set (GA E a → ℂ))
    (hT : ∀ G ∈ T, G ∈ bddForms E a ω) (hTr : ∀ G ∈ T, ∀ h : GA E a, (fun g => G (g * h)) ∈ T)
    (h0 : ∀ φ ∈ π.V, ∀ G ∈ T, pet (latticeGL E a) μ φ.1 G = 0) {F : GA E a → ℂ} (hF : F ∈ mspanR π) :
    F ∈ bddForms E a ω ∧ ∀ G ∈ T, pet (latticeGL E a) μ F G = 0 := by
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ bddForms E a ω ∧ ∀ G ∈ T, pet (latticeGL E a) μ F G = 0}
      add_mem' := fun {F F'} hF hF' => ⟨add_mem hF.1 hF'.1, fun G hG => by
        rw [pet_add_left μ hω hF.1 hF'.1 (hT G hG), hF.2 G hG, hF'.2 G hG, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun G _ => by simp [pet, descend]⟩
      smul_mem' := fun c F hF => ⟨Submodule.smul_mem _ c hF.1, fun G hG => by
        rw [pet_smul_left, hF.2 G hG, mul_zero]⟩ }
  have htr : ∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S := fun F hF h =>
    ⟨mul_right_mem_bddForms hF.1 h, fun G hG => by
      rw [pet_mul_right_left μ hω hF.1 (hT G hG) h]; exact hF.2 _ (hTr G hG h⁻¹)⟩
  refine Submodule.mem_sInf.1 hF S ⟨fun φ hφ => ⟨mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ,
    fun G hG => h0 φ hφ G hG⟩, htr, fun F hF X _ ν _ k γ hk => ⟨kerInf_mem_bddForms hk hF.1, fun G hG => ?_⟩⟩
  rw [pet_kerInf_left μ hω hk hF.1 (hT G hG)]
  exact integral_eq_zero_of_ae (.of_forall fun x => mul_eq_zero_of_right _ ((htr F hF _).2 G hG))

end Lemmas

theorem setIntegral_mspanR_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π π'' : CuspSub E a) (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → π''.HasCentChar ω →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure],
    (∀ φ ∈ π.V, ∀ φ'' ∈ π''.V, GlobalTheory.AutomorphicL2Unitary.pet (latticeGL E a) μ φ.1 φ''.1 = 0) →
    ∀ 𝓕' : Set (GA E a), IsFundamentalDomain (latticeGL E a) 𝓕' μ →
    ∀ F ∈ GlobalTheory.JSW.mspanR π, ∀ F'' ∈ GlobalTheory.JSW.mspanR π'', ∫ g in 𝓕', F g * starRingEnd ℂ (F'' g) ∂μ = 0 := by
  intro E _ _ _ a _ π π'' ω hω hπ hπ'' μ _ h0 𝓕' h𝓕 F hF F'' hF''
  have hB := GlobalTheory.CuspOrth.cuspFormsBounded
  have base : ∀ φ ∈ π.V, ∀ ψ ∈ π''.V, ∀ h : GA E a, pet (latticeGL E a) μ φ.1 (fun g => ψ.1 (g * h)) = 0 := by
    intro φ hφ ψ hψ h
    have e := pet_mul_right_left μ hω (mem_bddForms_of_cuspSub hB hω hπ hφ) (mem_bddForms_of_cuspSub hB hω hπ'' hψ) h⁻¹
    rw [inv_inv] at e
    rw [← e]
    obtain ⟨y, k, e'⟩ : ∃ y k, h⁻¹ = infGL E a y * finGL E a k := ⟨_, _, (infGL_mul_finGL h⁻¹).symm⟩
    rw [e']
    have H := (GlobalTheory.KeepOrth.pet_eq_zero_of_orthogonal hB E a π π'' ω hω hπ hπ'' μ h0).1 (act (.fin k) φ)
      (π.stable (.fin k) φ hφ) ψ hψ y
    refine Eq.trans (congrArg (fun F => pet (latticeGL E a) μ F ψ.1) (funext fun g => ?_)) H
    show φ.1 (g * (infGL E a y * finGL E a k)) = (act (.fin k) φ).1 (g * infGL E a y)
    rw [← mul_assoc]; rfl
  have A1 := fun {F} (hF : F ∈ mspanR π) => mspanR_pet_eq_zero μ hω hπ
    {G | ∃ ψ ∈ π''.V, ∃ h : GA E a, G = fun g => ψ.1 (g * h)}
    (by rintro _ ⟨ψ, hψ, h, rfl⟩; exact mul_right_mem_bddForms (mem_bddForms_of_cuspSub hB hω hπ'' hψ) h)
    (by rintro _ ⟨ψ, hψ, h, rfl⟩ k; exact ⟨ψ, hψ, k * h, funext fun g => by simp only [mul_assoc]⟩)
    (by rintro φ hφ _ ⟨ψ, hψ, h, rfl⟩; exact base φ hφ ψ hψ h) hF
  have A2 := fun {G} (hG : G ∈ mspanR π'') => mspanR_pet_eq_zero μ hω hπ'' (mspanR π : Set (GA E a → ℂ))
    (fun F hF => (A1 hF).1) (fun F hF h => mul_right_mem_mspanR hF h)
    (fun ψ hψ F hF => by
      rw [← conj_pet, (A1 hF).2 _ ⟨ψ, hψ, 1, funext fun g => by rw [mul_one]⟩, map_zero]) hG
  obtain ⟨bF'', h2⟩ := A2 hF''
  rw [← (pet_eq_setIntegral hω (A1 hF).1 bF'' h𝓕).2, ← conj_pet, h2 F hF, map_zero]

end GlobalTheory.MspanROrth
