import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfI

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

namespace OntoJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Dt (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (la : Wt X.Ψ r)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X la P ∧
    ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z

open Classical in

def TL {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℂ) : Lp ℂ 2 ν :=
  if h : MemLp f 2 ν then h.toLp f else 0

section TLs

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

theorem TL_eq {f : α → ℂ} (h : MemLp f 2 ν) : TL ν f = h.toLp f := by
  unfold TL
  rw [dif_pos h]

theorem TL_congr {f g : α → ℂ} (hf : MemLp f 2 ν) (hfg : f =ᵐ[ν] g) : TL ν f = TL ν g := by
  rw [TL_eq hf, TL_eq (hf.ae_eq hfg)]
  exact (MemLp.toLp_eq_toLp_iff _ _).2 hfg

theorem TL_add {f g : α → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    TL ν (f + g) = TL ν f + TL ν g := by
  rw [TL_eq (hf.add hg), TL_eq hf, TL_eq hg]
  exact MemLp.toLp_add hf hg

theorem TL_sub {f g : α → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    TL ν (f - g) = TL ν f - TL ν g := by
  rw [TL_eq (hf.sub hg), TL_eq hf, TL_eq hg]
  exact MemLp.toLp_sub hf hg

theorem TL_smul {f : α → ℂ} (a : ℂ) (hf : MemLp f 2 ν) : TL ν (a • f) = a • TL ν f := by
  rw [TL_eq (hf.const_smul a), TL_eq hf]
  exact MemLp.toLp_const_smul a hf

theorem TL_zero : TL ν (0 : α → ℂ) = 0 := by
  rw [TL_eq MeasureTheory.MemLp.zero]
  exact MemLp.toLp_zero _

end TLs

variable (X : Data E r) (x0 : Frame X.Ψ r) {W : Frame X.Ψ r → ℝ≥0∞} {bb : ℝ} {la : Wt X.Ψ r}

theorem ka_cont : ContinuousOn (kaF X x0 bb) (OmF X x0) :=
  fun _ hz => (ka_contDiffAt bb hz).continuousAt.continuousWithinAt

theorem aemF (hWm : Measurable W) {F : V (nd X) → ℂ} (hF : ContinuousOn F (OmF X x0)) :
    AEMeasurable (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) (muF X x0) := by
  have h1 : ContinuousOn (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z)) (OmF X x0) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((hF.norm.pow 2).div (ka_cont X x0) fun z _ => (Real.exp_pos _).ne')
  have h2 : Measurable fun z => W (cpt X x0 z) := hWm.comp (cd_cpt X x0).continuous.measurable
  have h3 : AEMeasurable (fun z => ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z))
      (volume.restrict (OmF X x0)) :=
    (h1.aemeasurable (isOpen_OmF X x0).measurableSet).mul h2.aemeasurable
  exact h3.mono_ac (withDensity_absolutelyContinuous _ _)

theorem Dt_zero : Dt X x0 W bb la (fun _ => 0) (fun _ => 0) := by
  refine ⟨differentiableOn_const _, ?_, ⟨differentiableOn_const _, fun _ _ _ _ => by simp⟩, fun _ _ => rfl⟩
  unfold InAt
  simp

theorem Dt_add (hWm : Measurable W) {F1 F2 : V (nd X) → ℂ} {P1 P2 : Frame X.Ψ r → ℂ}
    (h1 : Dt X x0 W bb la F1 P1) (h2 : Dt X x0 W bb la F2 P2) :
    Dt X x0 W bb la (fun z => F1 z + F2 z) (fun y => P1 y + P2 y) := by
  refine ⟨h1.1.add h2.1, ?_, ⟨h1.2.2.1.1.add h2.2.2.1.1, fun x hx b hb => ?_⟩, fun z hz => ?_⟩
  · unfold InAt
    refine lt_of_le_of_lt (lint_add_le (k := kaF X x0 bb) (fun z => Real.exp_pos _)
      (aemF X x0 hWm h1.1.continuousOn)) ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) h1.2.1, ENNReal.mul_lt_top (by simp) h2.2.1⟩
  · beta_reduce
    rw [h1.2.2.1.2 x hx b hb, h2.2.2.1.2 x hx b hb]
    ring
  · beta_reduce
    rw [h1.2.2.2 z hz, h2.2.2.2 z hz]

theorem Dt_smul (a : ℂ) {F : V (nd X) → ℂ} {P : Frame X.Ψ r → ℂ} (h : Dt X x0 W bb la F P) :
    Dt X x0 W bb la (fun z => a * F z) (fun y => a * P y) := by
  refine ⟨h.1.const_mul a, ?_, ⟨h.2.2.1.1.const_mul a, fun x hx b hb => ?_⟩, fun z hz => ?_⟩
  · have heq : ∀ z, ENNReal.ofReal (‖a * F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) =
        ENNReal.ofReal (‖a‖ ^ 2) * (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := by
      intro z
      rw [norm_mul, mul_pow, mul_div_assoc, ENNReal.ofReal_mul (by positivity), mul_assoc]
    unfold InAt
    simp_rw [heq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.2.1
  · beta_reduce
    rw [h.2.2.1.2 x hx b hb]
    ring
  · beta_reduce
    rw [h.2.2.2 z hz]

end OntoJ

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
