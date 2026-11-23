import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.FcCls

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} [MeasurableSpace (G n)]

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  show Matrix.det y.val ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

theorem cls_eq_toLp (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {f : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f = hf.toLp _ := by
  rw [cls, dif_pos hf]

theorem continuous_lift {V : Type} [TopologicalSpace V] {f : Mat n → V}
    (hf : ContinuousOn f (GLs n)) : Continuous (fun y : G n => f y.val) := by
  exact hf.comp_continuous Units.continuous_val (fun y => val_mem_GLs y)

theorem cls_congr (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {f f' : Mat n → V} (h : ∀ g ∈ GLs n, f g = f' g) : cls μ f = cls μ f' := by
  have hff : (fun y : G n => f y.val) = fun y => f' y.val := funext fun y => h _ (val_mem_GLs y)
  unfold cls
  rw [hff]

theorem cls_unique [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {f f' : Mat n → V}
    (hc : ContinuousOn f (GLs n)) (hc' : ContinuousOn f' (GLs n))
    (hf : MemLp (fun y : G n => f y.val) 2 μ) (hf' : MemLp (fun y : G n => f' y.val) 2 μ)
    (h : cls μ f = cls μ f') : ∀ g ∈ GLs n, f g = f' g := by
  intro g hg
  rw [cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := f') μ hf'] at h
  have h1 := (MemLp.toLp_eq_toLp_iff hf hf').1 h
  have h2 := (Continuous.ae_eq_iff_eq μ (continuous_lift hc) (continuous_lift hc')).1 h1
  have hu : IsUnit (Matrix.det g) := isUnit_iff_ne_zero.2 hg
  exact congrFun h2 (Matrix.nonsingInvUnit g hu)

theorem cls_add_smul (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (a : ℂ) {f f' : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hf' : MemLp (fun y : G n => f' y.val) 2 μ) : cls μ (a • f + f') = a • cls μ f + cls μ f' := by
  have hs : MemLp (fun y : G n => (a • f + f') y.val) 2 μ := (hf.const_smul a).add hf'
  rw [cls_eq_toLp (f := a • f + f') μ hs, cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := f') μ hf',
    ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
  rfl

theorem rR_cls [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (hU : Unimod) (h : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) :
    rR μ V h (cls μ f) = cls μ (fun y => f (y * h.val)) := by
  have hmp : MeasurePreserving (fun y : G n => y * h) μ μ := by
    have := (hU n μ).1
    exact measurePreserving_mul_right μ h
  rw [cls_eq_toLp (f := f) μ hf,
    cls_eq_toLp (f := fun y => f (y * h.val)) μ (hf.comp_measurePreserving hmp)]
  unfold rR
  rw [dif_pos hmp]
  exact Lp.toLp_compMeasurePreserving hf hmp

theorem compLpL_cls (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : V →L[ℂ] V) {f : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ) :
    A.compLpL 2 μ (cls μ f) = cls μ (fun y => A (f y)) := by
  have hA : MemLp (fun y : G n => A (f y.val)) 2 μ := A.comp_memLp' hf
  rw [cls_eq_toLp (f := f) μ hf, cls_eq_toLp (f := fun y => A (f y)) μ hA]
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (p := 2) (μ := μ) (hf.toLp _), MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hA]
    with y h1 h2 h3
  rw [h1, h2, h3]

theorem clsFacts : ClsFacts := by
  intro n _ _ μ _ V _ _ hU
  exact ⟨fun f f' hc hc' hf hf' h => cls_unique μ hc hc' hf hf' h,
    fun a f f' hf hf' => cls_add_smul μ a hf hf',
    fun f f' h => cls_congr μ h,
    fun h f hf => rR_cls μ hU h hf,
    fun A f hf => compLpL_cls μ A hf⟩

end GlobalTheory.CompanionTheory.FcCls
