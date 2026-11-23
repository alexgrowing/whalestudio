import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral

noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.ConstTermSmooth UpperTheory.V.Cm
open scoped ContDiff

namespace UpperTheory.ConvolutionTheory.BW.SliceClasses

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
  {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (p : Y → GA E a) (w : Y → ℂ)

def avg (F : GA E a → ℂ) (g : GA E a) : ℂ := ∫ y, F (p y * g) * w y ∂ν

structure Cls (Gd : Sm E a → Prop) : Prop where
  lie : ∀ F X, Gd F → Gd (lie E a X F)
  meas : ∀ F, Gd F → ∀ g, AEStronglyMeasurable (fun y => F.1 (p y * g) * w y) ν
  bdd : ∀ F, Gd F → ∀ K : Set (GA E a), IsCompact K → ∃ C : ℝ, ∀ y, ∀ g ∈ K, ‖F.1 (p y * g) * w y‖ ≤ C

variable {ν p w} {Gd : Sm E a → Prop} [IsFiniteMeasure ν]

theorem Cls.integrable (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) (g : GA E a) :
    Integrable (fun y => F.1 (p y * g) * w y) ν := by
  obtain ⟨C, hC⟩ := h.bdd F hF {g} isCompact_singleton
  exact Integrable.of_bound (h.meas F hF g) C (.of_forall fun y => hC y g rfl)

private theorem chart_unit (F : GA E a → ℂ) (g g' : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart F (g' * g) x = F (g' * (g * infGL E a (IsUnit.unit (hx : IsUnit (Matrix.of x))))) := by
  rw [← mul_assoc]
  exact chart_val F _ (IsUnit.unit (hx : IsUnit (Matrix.of x)))

private theorem Cls.integrable_chart (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) (g : GA E a) {x : Lie E a}
    (hx : x ∈ invSet E a) : Integrable (fun y => chart F.1 (p y * g) x * w y) ν := by
  simp only [chart_unit F.1 g _ hx]
  exact h.integrable hF _

private theorem Cls.bdd_chart (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) (g : GA E a) {S : Set (Lie E a)}
    (hS : IsCompact S) (hSU : S ⊆ invSet E a) : ∃ C : ℝ, ∀ y, ∀ x ∈ S, ‖chart F.1 (p y * g) x * w y‖ ≤ C := by
  have hu : Continuous fun x : S => (IsUnit.unit (hSU x.2 : IsUnit (Matrix.of x.1)) : GL (Fin a) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have := contDiffOn_invM.continuousOn.comp_continuous (f := fun x : S => x.1) continuous_subtype_val fun x => hSU x.2
    refine Continuous.congr this fun p => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  haveI : CompactSpace S := isCompact_iff_compactSpace.1 hS
  obtain ⟨C, hC⟩ := h.bdd F hF _ (isCompact_range ((continuous_const (y := g)).mul (continuous_infGL.comp hu)))
  refine ⟨C, fun y x hx => ?_⟩
  rw [chart_unit F.1 g _ (hSU hx)]
  exact hC y _ ⟨⟨x, hx⟩, rfl⟩

omit [IsFiniteMeasure ν] in
private theorem chart_avg (F : GA E a → ℂ) (g : GA E a) :
    chart (avg ν p w F) g = fun x => ∫ y, chart F (p y * g) x * w y ∂ν := by
  funext x
  by_cases h : IsUnit (Matrix.of x)
  · simp only [chart, avg, dif_pos h, mul_assoc]
  · simp only [chart, dif_neg h, zero_mul, integral_zero]

private theorem Cls.hasFDerivAt (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) (g : GA E a) {x : Lie E a}
    (hx : x ∈ invSet E a) : HasFDerivAt (chart (avg ν p w F.1) g)
      (∑ i, chart (avg ν p w (GlobalTheory.CuspRep.lie E a (Module.finBasis ℝ (Lie E a) i) F).1) g x • coef i x) x := by
  obtain ⟨S, hSy, hSU, hS⟩ := local_compact_nhds (isOpen_invSet.mem_nhds hx)
  choose C hC using fun i => h.bdd_chart (h.lie F (Module.finBasis ℝ (Lie E a) i) hF) g hS hSU
  choose D hD using fun i => hS.exists_bound_of_continuousOn ((contDiffOn_coef (E := E) (a := a) i).continuousOn.mono hSU)
  have hi : ∀ i, Integrable (fun y => (chart (GlobalTheory.CuspRep.lie E a (Module.finBasis ℝ (Lie E a) i) F).1 (p y * g) x * w y) • coef i x) ν :=
    fun i => (h.integrable_chart (h.lie F _ hF) g hx).smul_const _
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun x y => chart F.1 (p y * g) x * w y)
    (F' := fun x y => ∑ i, (chart (GlobalTheory.CuspRep.lie E a (Module.finBasis ℝ (Lie E a) i) F).1 (p y * g) x * w y) • coef i x)
    (bound := fun _ => ∑ i, C i * D i) hSy
    (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) fun z hz => (h.integrable_chart hF g hz).1)
    (h.integrable_chart hF g hx) (integrable_finset_sum _ fun i _ => hi i).1
    (.of_forall fun y z hz => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
      rw [norm_smul]
      exact mul_le_mul (hC i y z hz) (hD i z hz) (norm_nonneg _) ((norm_nonneg _).trans (hC i y z hz))))
    (integrable_const _) (.of_forall fun y z hz => by
      have h1 := (((contDiffAt_chart F.2 (p y * g) (hSU hz)).differentiableAt (by simp)).hasFDerivAt).mul_const (w y)
      rw [fderiv_chart F _ (hSU hz), Finset.smul_sum] at h1
      simp only [smul_smul, mul_comm (w y)] at h1
      exact h1)
  rw [integral_finset_sum _ fun i _ => hi i] at key
  simp only [integral_smul_const] at key
  simp only [chart_avg]
  exact key

theorem Cls.mem_Sm (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) : avg ν p w F.1 ∈ Sm E a := by
  intro g
  have key : ∀ n : ℕ, ∀ F : Sm E a, Gd F → ContDiffOn ℝ n (chart (avg ν p w F.1) g) (invSet E a) := by
    intro n
    induction n with
    | zero =>
      intro F hF
      exact contDiffOn_zero.2 fun y hy => (h.hasFDerivAt hF g hy).continuousAt.continuousWithinAt
    | succ n ih =>
      intro F hF
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet]
      refine ⟨fun y hy => (h.hasFDerivAt hF g hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      refine ContDiffOn.congr ?_ fun y hy => (h.hasFDerivAt hF g hy).fderiv
      exact ContDiffOn.sum fun i _ => (ih _ (h.lie _ _ hF)).smul ((contDiffOn_coef i).of_le (by exact_mod_cast le_top))
  exact contDiffOn_infty.2 fun n => key n F hF

theorem Cls.lieD_avg (h : Cls ν p w Gd) {F : Sm E a} (hF : Gd F) (X : Lie E a) (g : GA E a) :
    lieD X (avg ν p w F.1) g = avg ν p w (GlobalTheory.CuspRep.lie E a X F).1 g := by
  have h1 : oneL E a ∈ invSet E a := isUnit_one
  rw [lieD, (h.hasFDerivAt hF g h1).fderiv]
  simp only [chart_avg, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ← integral_mul_const]
  rw [← integral_finset_sum _ fun i _ => (h.integrable_chart (h.lie F _ hF) g h1).mul_const _]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [lie_apply, lieD]
  rw [fderiv_chart F _ h1]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end UpperTheory.ConvolutionTheory.BW.SliceClasses
