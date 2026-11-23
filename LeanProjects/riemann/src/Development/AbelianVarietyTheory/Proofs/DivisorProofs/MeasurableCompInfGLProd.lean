import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PetEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

noncomputable section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Petersson Formalism.L2.Host
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped ComplexConjugate

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem measurable_chart_prod {φ : GA E a → ℂ} (hφ : Continuous φ) :
    Measurable fun p : GA E a × Lie E a => chart φ p.1 p.2 := by
  classical
  have e : (fun p : GA E a × Lie E a => chart φ p.1 p.2) =
      (Set.univ ×ˢ invSet E a).piecewise (fun p : GA E a × Lie E a => chart φ p.1 p.2) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ Set.univ ×ˢ invSet E a
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      have hp' : ¬ IsUnit (Matrix.of p.2) := fun h => hp ⟨trivial, h⟩
      exact dif_neg hp'
  rw [e]
  exact (GlobalTheory.ConstTermSmooth.continuousOn_chart hφ).measurable_piecewise continuousOn_const
    (isOpen_univ.prod isOpen_invSet).measurableSet

theorem measurable_comp_infGL_prod {F : GA E a → ℂ} (hF : Continuous F) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun p : GA E a × X => F (p.1 * infGL E a (γ p.2)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun p : GA E a × X => F (p.1 * infGL E a (γ p.2))) =
      (fun p : GA E a × Lie E a => chart F p.1 p.2) ∘ fun p : GA E a × X => (p.1, toL (γ p.2).val) :=
    funext fun p => (chart_val F p.1 (γ p.2)).symm
  rw [e]
  exact (measurable_chart_prod hF).comp (measurable_fst.prodMk (h.comp measurable_snd))

theorem IsRapidInf.integrable_norm {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) : Integrable (fun x => ‖k x‖) ν := by
  simpa using hk.2.2 0

theorem kerInf_mem_bddForms {ω : HChar E} {F : GA E a → ℂ} (h : F ∈ bddForms E a ω) {X : Type} [MeasurableSpace X]
    {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ bddForms E a ω := by
  obtain ⟨C, hC⟩ := h.2.2.2
  have hki := hk.integrable_norm
  have hm := measurable_comp_infGL_prod h.1 hk.2.1
  refine ⟨?_, fun γ' g => ?_, fun z g => ?_, ∫ x, ‖k x‖ * C ∂ν, fun g => ?_⟩
  · refine continuous_of_dominated (bound := fun x => ‖k x‖ * C)
      (fun g => (hk.1.mul (hm.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
      (fun g => .of_forall fun x => ?_) (hki.mul_const C)
      (.of_forall fun x => continuous_const.mul (h.1.comp (continuous_mul_const _)))
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · simp only [kerInf, mul_assoc, h.2.1]
  · rw [kerInf, kerInf, ← integral_const_mul]
    congr 1; funext x; rw [mul_assoc, h.2.2.1]; ring
  · exact norm_integral_le_of_norm_le (hki.mul_const C)
      (.of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem pet_kerInf_left {ω : HChar E} (hω : ω.IsUnitary) {F ψ : GA E a → ℂ} (h : F ∈ bddForms E a ω)
    (h' : ψ ∈ bddForms E a ω) {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    pet (latticeGL E a) μ (kerInf ν k γ F) ψ =
      ∫ x, k x * pet (latticeGL E a) μ (fun g => F (g * infGL E a (γ x))) ψ ∂ν := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hD := isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI : IsFiniteMeasure (μ.restrict (stdDom (latticeGL E a))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ hD]; exact measure_lt_top _ _⟩
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD'⟩ := h'.2.2.2
  have hki := hk.integrable_norm
  have hm := measurable_comp_infGL_prod h.1 hk.2.1
  have hi : Integrable (fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1))
      ((μ.restrict (stdDom (latticeGL E a))).prod ν) := by
    refine ((integrable_const (C * D)).mul_prod hki).mono'
      (((hk.1.comp measurable_snd).mul hm).mul
        ((Complex.continuous_conj.comp h'.1).measurable.comp measurable_fst)).aestronglyMeasurable
      (.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD' _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC 1))) (norm_nonneg _)
  rw [(pet_eq_setIntegral hω (kerInf_mem_bddForms h hk) h' hD).2]
  simp only [kerInf, ← integral_mul_const]
  rw [integral_integral_swap hi]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [(pet_eq_setIntegral hω (mul_right_mem_bddForms h _) h' hD).2, ← integral_const_mul, mul_assoc]

theorem rspan_central {π : CuspSub E a} {ω : HChar E} (hπ : π.HasCentChar ω) {F : GA E a → ℂ} (hF : F ∈ rspan π)
    (z : Ideles E) (g : GA E a) :
    F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g := by
  have hc := CuspSub.hasCentral_iff.2 hπ
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ (z : Ideles E) g, F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g}
      add_mem' := fun {F F'} hF hF' z g => by simp only [Pi.add_apply, hF z g, hF' z g, mul_add]
      zero_mem' := fun z g => by simp
      smul_mem' := fun c F hF z g => by simp only [Pi.smul_apply, smul_eq_mul, hF z g]; ring }
  refine rspan_le (S := S) (fun φ hφ z g => hc.apply hφ z g) (fun F hF h z g => ?_)
    (fun F hF X _ ν _ k γ _ z g => ?_) hF z g
  · change F (GeneralLinearGroup.scalar (Fin a) z * g * h) = _ * F (g * h)
    rw [mul_assoc]; exact hF z _
  · change ∫ x, k x * F (GeneralLinearGroup.scalar (Fin a) z * g * infGL E a (γ x)) ∂ν =
      _ * ∫ x, k x * F (g * infGL E a (γ x)) ∂ν
    rw [← integral_const_mul]
    congr 1; funext x; rw [mul_assoc, hF z]; ring

theorem pet_rt_eq_zero {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) {ψ : GA E a → ℂ}
    (hψ : ψ ∈ bddForms E a ω) (h0 : ∀ φ ∈ π.V, pet (latticeGL E a) μ φ.1 ψ = 0) {φ : Sm E a} (hφ : φ ∈ π.V)
    (h : GA E a) : pet (latticeGL E a) μ (fun g => φ.1 (g * h)) ψ = 0 := by
  have hb : ∀ φ ∈ π.V, φ.1 ∈ bddForms E a ω := fun φ hφ =>
    mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ
  rw [← infGL_mul_finGL h]
  have e : (fun g => φ.1 (g * (infGL E a (GeneralLinearGroup.map (pInf E) h) *
      finGL E a (GeneralLinearGroup.map (pFin E) h)))) =
      fun g => (finRep E a (GeneralLinearGroup.map (pFin E) h) φ).1 (g * infGL E a (GeneralLinearGroup.map (pInf E) h)) := by
    funext g
    change _ = φ.1 (g * infGL E a _ * finGL E a _)
    rw [mul_assoc]
  rw [e]
  exact GlobalTheory.KeepOrth.pet_translate_eq_zero μ hω hψ hb (fun X => π.stable (.lie X)) (fun φ hφ => (π.cusp φ hφ).1) h0
    (π.stable (.fin _) φ hφ) _

theorem rspan_bdd_pet_eq_zero {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω)
    {ψ : GA E a → ℂ} (hψ : ψ ∈ bddForms E a ω) (h0 : ∀ φ ∈ π.V, pet (latticeGL E a) μ φ.1 ψ = 0)
    {F : GA E a → ℂ} (hF : F ∈ rspan π) :
    F ∈ bddForms E a ω ∧ ∀ h : GA E a, pet (latticeGL E a) μ F (fun g => ψ (g * h)) = 0 := by
  have hψh : ∀ h : GA E a, (fun g => ψ (g * h)) ∈ bddForms E a ω := mul_right_mem_bddForms hψ
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ bddForms E a ω ∧ ∀ h : GA E a, pet (latticeGL E a) μ F (fun g => ψ (g * h)) = 0}
      add_mem' := fun {F F'} hF hF' => ⟨add_mem hF.1 hF'.1, fun h => by
        rw [pet_add_left μ hω hF.1 hF'.1 (hψh h), hF.2 h, hF'.2 h, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun h => by simp [pet, descend]⟩
      smul_mem' := fun c F hF => ⟨Submodule.smul_mem _ c hF.1, fun h => by
        rw [pet_smul_left, hF.2 h, mul_zero]⟩ }
  have htr : ∀ F ∈ S, ∀ h' : GA E a, (fun g => F (g * h')) ∈ S := fun F hF h' =>
    ⟨mul_right_mem_bddForms hF.1 h', fun h => by
      rw [pet_mul_right_left μ hω hF.1 (hψh h) h']
      have := hF.2 (h'⁻¹ * h)
      simp only [mul_assoc] at this ⊢
      exact this⟩
  refine rspan_le (S := S) (fun φ hφ => ⟨mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ,
    fun h => ?_⟩) htr (fun F hF X _ ν _ k γ hk => ⟨kerInf_mem_bddForms hF.1 hk, fun h => ?_⟩) hF
  · have hb := mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ
    have e := pet_mul_right_left μ hω hb hψ h⁻¹
    rw [inv_inv] at e
    rw [← e]
    exact pet_rt_eq_zero μ hω hπ hψ h0 hφ h⁻¹
  · rw [pet_kerInf_left μ hω hF.1 (hψh h) ν hk]
    exact integral_eq_zero_of_ae (.of_forall fun x => mul_eq_zero_of_right _ ((htr F hF _).2 h))

example {π : CuspSub E a} {ω : HChar E} (hπ : π.HasCentChar ω) {φ : Sm E a} (hφ : φ ∈ π.V) (z : Ideles E) (g : GA E a) :
    φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g :=
  rspan_central hπ (mem_rspan hφ) z g

end GlobalTheory.JSW
