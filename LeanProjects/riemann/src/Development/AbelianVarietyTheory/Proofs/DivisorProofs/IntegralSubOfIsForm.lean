import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompactStatement

set_option autoImplicit false

noncomputable section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder ENNReal
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def reDens (α : A.Fld) (i : A.ι) (v : V n) : ℝ := (dens (A.loc α i v)).re

theorem loc_sub (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α - β) i v = A.loc α i v - A.loc β i v := by
  unfold loc; split_ifs
  · rfl
  · exact (sub_zero 0).symm

theorem dens_sub' (x y : Alt n) : dens (x - y) = dens x - dens y := by
  simp only [dens, map_sub, Finsupp.sub_apply, sub_div]

theorem reDens_sub (α β : A.Fld) (i : A.ι) (v : V n) : A.reDens (α - β) i v = A.reDens α i v - A.reDens β i v := by
  simp only [reDens, loc_sub, dens_sub', Complex.sub_re]

theorem reDens_compat {α : A.Fld} (hα : A.IsForm α) (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source)
    (hj : y ∈ (A.e j).source) :
    A.reDens α i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * A.reDens α j (A.e j y) := by
  have h1 := A.loc_crd α (⟨(i, y), hi⟩ : A.Pt)
  have h2 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
  have h3 := hα.compat (⟨(i, y), hi⟩ : A.Pt) ⟨(j, y), hj⟩ rfl
  simp only [reDens]
  erw [h1, h2, h3, GlobalTheory.T.topDegreeDensity_pullback_eq_normSq_det_mul]
  rw [Complex.re_ofReal_mul]
  rfl

theorem continuousOn_reDens {α : A.Fld} (hα : A.IsForm α) (i : A.ι) :
    ContinuousOn (A.reDens α i) (A.e i).target := by
  have := (hα.smooth i Finset.univ).continuousOn
  exact Complex.continuous_re.comp_continuousOn (this.div_const _)

theorem aemeasurable_ofReal_chart [MeasurableSpace M] (e : OpenPartialHomeomorph M (V n)) (r : V n → ℝ)
    (hr : ContinuousOn r e.target) :
    AEMeasurable (fun v => ENNReal.ofReal (r (e (e.symm v)))) (volume.restrict (e.target ∩ e.symm ⁻¹' univ)) := by
  rw [preimage_univ, inter_univ]
  have h := (ENNReal.continuous_ofReal.comp_continuousOn hr).aemeasurable (μ := volume) e.open_target.measurableSet
  refine h.congr ((ae_restrict_iff' e.open_target.measurableSet).2 (Filter.Eventually.of_forall fun v hv => ?_))
  simp [e.right_inv hv]

theorem ofReal_compat (r : A.ι → V n → ℝ)
    (hc : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y))
    (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source) (hj : y ∈ (A.e j).source) :
    ENNReal.ofReal (r i (A.e i y)) =
      ENNReal.ofReal (‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2) * ENNReal.ofReal (r j (A.e j y)) := by
  rw [hc i j y hi hj, ENNReal.ofReal_mul (by positivity)]

theorem glueMeas_add_three [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] (r₁ r₂ r₃ : A.ι → V n → ℝ)
    (hr₁ : ∀ i, ContinuousOn (r₁ i) (A.e i).target) (hr₂ : ∀ i, ContinuousOn (r₂ i) (A.e i).target)
    (hc₁ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₁ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₁ j (A.e j y))
    (hc₂ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₂ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₂ j (A.e j y))
    (hc₃ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₃ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₃ j (A.e j y)) :
    ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)) +
      ENNReal.ofReal (r₃ i (A.e i y))) univ =
    ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) univ +
      ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₂ i (A.e i y))) univ +
      ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₃ i (A.e i y))) univ := by
  have c₁ := A.ofReal_compat r₁ hc₁
  have c₂ := A.ofReal_compat r₂ hc₂
  have c₃ := A.ofReal_compat r₃ hc₃
  rw [ChartGlue.glueMeas_add_of_compat_on A.e A.holo A.cover MeasurableSet.univ
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i y => ENNReal.ofReal (r₃ i (A.e i y)))
      (fun i j y _ hi hj => by rw [c₁ i j y hi hj, c₂ i j y hi hj, mul_add])
      (fun i j y _ hi hj => c₃ i j y hi hj)
      (fun i => (aemeasurable_ofReal_chart (A.e i) _ (hr₁ i)).add (aemeasurable_ofReal_chart (A.e i) _ (hr₂ i))),
    ChartGlue.glueMeas_add_of_compat_on A.e A.holo A.cover MeasurableSet.univ
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) (fun i y => ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i j y _ hi hj => c₁ i j y hi hj) (fun i j y _ hi hj => c₂ i j y hi hj)
      (fun i => aemeasurable_ofReal_chart (A.e i) _ (hr₁ i))]

theorem ofReal_posNeg (x y : ℝ) :
    ENNReal.ofReal (x - y) + ENNReal.ofReal (-x) + ENNReal.ofReal y =
      ENNReal.ofReal (-(x - y)) + ENNReal.ofReal x + ENNReal.ofReal (-y) := by
  have m : ∀ t : ℝ, ENNReal.ofReal t = ENNReal.ofReal (max t 0) := fun t => by
    rcases le_total t 0 with h | h
    · simp [h, ENNReal.ofReal_of_nonpos h]
    · simp [h]
  have k : max (x - y) 0 + max (-x) 0 + max y 0 = max (-(x - y)) 0 + max x 0 + max (-y) 0 := by
    simp only [max_def]; split_ifs <;> linarith
  rw [m (x - y), m (-x), m y, m (-(x - y)), m x, m (-y),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _), k]

theorem integral_sub [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    (α β : A.Fld) (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.integral (α - β) = A.integral α - A.integral β := by
  have hF := A.reDens_compat hα
  have hG := A.reDens_compat hβ
  have cF := A.continuousOn_reDens hα
  have cG := A.continuousOn_reDens hβ

  let lin (c d : ℝ) : A.ι → V n → ℝ := fun i v => c * A.reDens α i v + d * A.reDens β i v
  have hlin (c d : ℝ) : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      lin c d i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * lin c d j (A.e j y) := by
    intro i j y hi hj
    simp only [lin, hF i j y hi hj, hG i j y hi hj]
    ring
  have clin (c d : ℝ) (i : A.ι) : ContinuousOn (lin c d i) (A.e i).target :=
    (continuousOn_const.mul (cF i)).add (continuousOn_const.mul (cG i))
  let P (c d : ℝ) : ℝ≥0∞ := ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (lin c d i (A.e i y))) univ
  have fin (c d : ℝ) : P c d ≠ ∞ :=
    GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn A.e A.cover A.holo (lin c d) (clin c d) (hlin c d)
  have part_eq (γ : A.Fld) (ε : ℤˣ) (c d : ℝ) (h : ∀ i v, ((ε : ℤ) : ℝ) * A.reDens γ i v = lin c d i v) :
      A.part γ ε univ = P c d := by
    simp only [part, P]
    congr 2
    funext i y
    rw [← h]
    rfl
  have e1 := part_eq (α - β) 1 1 (-1) fun i v => by simp [lin, reDens_sub]; ring
  have e2 := part_eq (α - β) (-1) (-1) 1 fun i v => by simp [lin, reDens_sub]; ring
  have e3 := part_eq α 1 1 0 fun i v => by simp [lin]
  have e4 := part_eq α (-1) (-1) 0 fun i v => by simp [lin]
  have e5 := part_eq β 1 0 1 fun i v => by simp [lin]
  have e6 := part_eq β (-1) 0 (-1) fun i v => by simp [lin]
  have key : P 1 (-1) + P (-1) 0 + P 0 1 = P (-1) 1 + P 1 0 + P 0 (-1) := by
    simp only [P]
    rw [← A.glueMeas_add_three _ _ _ (clin _ _) (clin _ _) (hlin _ _) (hlin _ _) (hlin _ _),
      ← A.glueMeas_add_three _ _ _ (clin _ _) (clin _ _) (hlin _ _) (hlin _ _) (hlin _ _)]
    congr 2
    funext i y
    have := ofReal_posNeg (A.reDens α i (A.e i y)) (A.reDens β i (A.e i y))
    simp only [lin]
    convert this using 3 <;> ring_nf
  have key' := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨fin _ _, fin _ _⟩) (fin _ _),
    ENNReal.toReal_add (fin _ _) (fin _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨fin _ _, fin _ _⟩) (fin _ _),
    ENNReal.toReal_add (fin _ _) (fin _ _)] at key'
  simp only [integral, Measure.real, e1, e2, e3, e4, e5, e6]
  linarith

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory.CxForm.HolAtlas

theorem integral_sub_of_isForm : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld),
    A.IsForm α → A.IsForm β → A.integral (α - β) = A.integral α - A.integral β :=
  fun A α β hα hβ => A.integral_sub α β hα hβ

end GlobalTheory.CxForm.HolAtlas
