import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.RealObj.RankOneTensors

open Formalism.L2.SG.RealObj

section Rk1

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

theorem norm_rankOneInnerOperator (a : V) (b : V') : ‖TermOp.rk1 a b‖ = ‖a‖ * ‖b‖ := by
  unfold TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem continuous_rankOneOperator {T : Type*} [TopologicalSpace T] {f : T → V} {g : T → V'} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => TermOp.rk1 (f x) (g x) := by
  have h1 : Continuous fun x => innerSL ℂ (g x) := (innerSL ℂ).continuous.comp hg
  have h2 : Continuous fun x => ContinuousLinearMap.smulRightL ℂ V' V (innerSL ℂ (g x)) :=
    (ContinuousLinearMap.smulRightL ℂ V' V).continuous.comp h1
  unfold TermOp.rk1
  exact h2.clm_apply hf

end Rk1

section Tens

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vt : Type*} [NormedAddCommGroup Vt] [InnerProductSpace ℂ Vt] (T : (∀ v, V v) → Vt)

theorem norm_tens (hT : ∀ x y, ⟪T x, T y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x : ∀ v, V v) : ‖T x‖ = ∏ v, ‖x v‖ := by
  have h := hT x x
  simp only [inner_self_eq_norm_sq_to_K] at h
  have h' : ‖T x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
    rw [← Finset.prod_pow]
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) two_ne_zero).1 h'

theorem tens_eq_zero (hT : ∀ x y, ⟪T x, T y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x : ∀ v, V v) (v0 : ι) (h0 : x v0 = 0) :
    T x = 0 := by
  rw [← norm_eq_zero, norm_tens T hT x]
  exact Finset.prod_eq_zero (Finset.mem_univ v0) (by rw [h0, norm_zero])

theorem eq_of_inner_tens (hS : Submodule.span ℂ (Set.range T) = ⊤) (a b : Vt)
    (h : ∀ z, ⟪T z, a⟫_ℂ = ⟪T z, b⟫_ℂ) : a = b := by
  rw [← sub_eq_zero]
  have hmem : ∀ w ∈ Submodule.span ℂ (Set.range T), ⟪w, a - b⟫_ℂ = 0 := by
    intro w hw
    refine Submodule.span_induction (fun y hy => ?_) ?_ (fun y z _ _ hy hz => ?_) (fun c y _ hy => ?_) hw
    · obtain ⟨z, rfl⟩ := hy
      rw [inner_sub_right, h z, sub_self]
    · exact inner_zero_left _
    · rw [inner_add_left, hy, hz, add_zero]
    · rw [inner_smul_left, hy, mul_zero]
  have h2 := hmem (a - b) (by rw [hS]; exact Submodule.mem_top)
  exact inner_self_eq_zero.mp h2

end Tens

section Fact

variable {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, MeasurableSpace (G v)] [∀ v, BorelSpace (G v)]
  [∀ v, SecondCountableTopology (G v)] (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)]
  {V V' : ι → Type*} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  [∀ v, FiniteDimensional ℂ (V v)] [∀ v, NormedAddCommGroup (V' v)] [∀ v, InnerProductSpace ℂ (V' v)]
  [∀ v, FiniteDimensional ℂ (V' v)]
  {Vt Vt' : Type*} [NormedAddCommGroup Vt] [InnerProductSpace ℂ Vt] [FiniteDimensional ℂ Vt]
  [NormedAddCommGroup Vt'] [InnerProductSpace ℂ Vt'] [FiniteDimensional ℂ Vt']
  (T : (∀ v, V v) → Vt) (T' : (∀ v, V' v) → Vt')
  (hT : ∀ x y, ⟪T x, T y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (hT' : ∀ x y, ⟪T' x, T' y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ)
  (hS : Submodule.span ℂ (Set.range T) = ⊤)
  (W : ∀ v, G v → V v) (W' : ∀ v, G v → V' v) (hW : ∀ v, Continuous (W v)) (hW' : ∀ v, Continuous (W' v))
  (Wt : (∀ v, G v) → Vt) (Wt' : (∀ v, G v) → Vt') (hWt : Continuous Wt) (hWt' : Continuous Wt')
  (hten : ∀ x, Wt x = T fun v => W v (x v)) (hten' : ∀ x, Wt' x = T' fun v => W' v (x v))

include hT hT' hS hW hW' hWt hWt' hten hten' in

theorem oo_factor (γ : ∀ v, G v) (y : ∀ v, V' v) :
    haveI : ∀ v, CompleteSpace (V v) := fun v => FiniteDimensional.complete ℂ (V v)
    haveI := FiniteDimensional.complete ℂ Vt
    (∫ x, TermOp.rk1 (Wt x) (Wt' (γ⁻¹ * x)) ∂(Measure.pi μ)) (T' y) =
      T fun v => (∫ s, TermOp.rk1 (W v s) (W' v ((γ v)⁻¹ * s)) ∂(μ v)) (y v) := by
  have : ∀ v, CompleteSpace (V v) := fun v => FiniteDimensional.complete ℂ (V v)
  have := FiniteDimensional.complete ℂ Vt
  let f : ∀ v, G v → (V' v →L[ℂ] V v) := fun v s => TermOp.rk1 (W v s) (W' v ((γ v)⁻¹ * s))
  let F : (∀ v, G v) → (Vt' →L[ℂ] Vt) := fun x => TermOp.rk1 (Wt x) (Wt' (γ⁻¹ * x))
  show (∫ x, F x ∂(Measure.pi μ)) (T' y) = T fun v => (∫ s, f v s ∂(μ v)) (y v)
  have hfc : ∀ v, Continuous (f v) := fun v =>
    continuous_rankOneOperator (hW v) ((hW' v).comp (continuous_const.mul continuous_id))
  have hFc : Continuous F := continuous_rankOneOperator hWt (hWt'.comp (continuous_const.mul continuous_id))
  have hnorm : ∀ x, ‖F x‖ = ∏ v, ‖f v (x v)‖ := by
    intro x
    simp only [F, f, norm_rankOneInnerOperator, hten, hten', norm_tens T hT, norm_tens T' hT', Finset.prod_mul_distrib]
    rfl
  have hzero : ∀ v0, ¬ Integrable (f v0) (μ v0) → (T fun v => (∫ s, f v s ∂(μ v)) (y v)) = 0 := by
    intro v0 h0
    refine tens_eq_zero T hT _ v0 ?_
    show (∫ s, f v0 s ∂(μ v0)) (y v0) = 0
    rw [integral_undef h0, ContinuousLinearMap.zero_apply]
  by_cases hF : Integrable F (Measure.pi μ)
  · by_cases hloc : ∀ v, Integrable (f v) (μ v)
    · refine eq_of_inner_tens T hS _ _ fun z => ?_
      rw [ContinuousLinearMap.integral_apply hF, ← integral_inner (hF.apply_continuousLinearMap _), hT]
      have hl : ∀ v, ⟪z v, (∫ s, f v s ∂(μ v)) (y v)⟫_ℂ =
          ∫ s, ⟪W' v ((γ v)⁻¹ * s), y v⟫_ℂ * ⟪z v, W v s⟫_ℂ ∂(μ v) := by
        intro v
        rw [ContinuousLinearMap.integral_apply (hloc v), ← integral_inner ((hloc v).apply_continuousLinearMap _)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        simp only [f, TermOp.rankOneInnerOperator_apply, inner_smul_right]
      have hp : ∀ x, ⟪T z, F x (T' y)⟫_ℂ = ∏ v, ⟪W' v ((γ v)⁻¹ * x v), y v⟫_ℂ * ⟪z v, W v (x v)⟫_ℂ := by
        intro x
        simp only [F, TermOp.rankOneInnerOperator_apply, inner_smul_right, hten, hten', hT, hT', Finset.prod_mul_distrib]
        rfl
      simp only [hl, hp]
      exact integral_fintype_prod_eq_prod (μ := μ)
        (fun v s => ⟪W' v ((γ v)⁻¹ * s), y v⟫_ℂ * ⟪z v, W v s⟫_ℂ)
    · push Not at hloc
      obtain ⟨v0, h0⟩ := hloc
      rw [hzero v0 h0]
      have h0' : ¬ Integrable (fun s => ‖f v0 s‖) (μ v0) := fun h =>
        h0 ((integrable_norm_iff (hfc v0).aestronglyMeasurable).1 h)
      have hprod : ∫ x, ∏ v, ‖f v (x v)‖ ∂(Measure.pi μ) = 0 := by
        have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := μ) (fun v s => ‖f v s‖)
        rw [this]
        exact Finset.prod_eq_zero (Finset.mem_univ v0) (integral_undef h0')
      have hint : Integrable (fun x => ∏ v, ‖f v (x v)‖) (Measure.pi μ) := by
        have := hF.norm
        simpa only [hnorm] using this
      have h00 := (integral_eq_zero_iff_of_nonneg
        (fun x => Finset.prod_nonneg fun v _ => norm_nonneg (f v (x v))) hint).1 hprod
      have hae : F =ᵐ[Measure.pi μ] 0 := h00.mono fun x hx => by
        have h1 : ‖F x‖ = 0 := by rw [hnorm]; simpa only [Pi.zero_apply] using hx
        simpa only [Pi.zero_apply] using norm_eq_zero.1 h1
      rw [integral_congr_ae hae]
      simp
  · rw [integral_undef hF, ContinuousLinearMap.zero_apply]
    by_cases hloc : ∀ v, Integrable (f v) (μ v)
    · exfalso
      apply hF
      have hP : Integrable (fun x => ∏ v, ‖f v (x v)‖) (Measure.pi μ) :=
        Integrable.fintype_prod_dep (fun v => (hloc v).norm)
      exact hP.mono' hFc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hnorm x).le)
    · push Not at hloc
      obtain ⟨v0, h0⟩ := hloc
      exact (hzero v0 h0).symm

end Fact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem OOFactor_holds {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : OOFactor X u u' := by
  intro γ y
  have h := oo_factor (fun v => Formalism.REAL.muG (X.B.I.ε v)) (X.tensU u) (X.tensU u') (X.tensU_inner u)
    (X.tensU_inner u') (X.tensU_span u) (X.Wloc u) (X.Wloc u') (X.Wloc_cont u) (X.Wloc_cont u')
    (X.Wu u) (X.Wu u') (X.Wu_spec u).2.2.1 (X.Wu_spec u').2.2.1 (X.Wu_tens u) (X.Wu_tens u') γ y
  simpa only [OOinf, Jv, TermOp.OO, Measure.restrict_univ] using h

end Formalism.L2.SG.RealObj.RankOneTensors
