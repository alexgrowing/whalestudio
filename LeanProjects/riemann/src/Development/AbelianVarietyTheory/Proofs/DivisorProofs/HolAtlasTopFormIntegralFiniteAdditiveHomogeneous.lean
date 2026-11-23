import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompactStatement

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
open GlobalTheory.CxForm GlobalTheory.ChartGlue

namespace GlobalTheory.LineForm.TopInt

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_add (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α + β) i v = A.loc α i v + A.loc β i v := by
  unfold HolAtlas.loc; split_ifs
  · rfl
  · exact (add_zero 0).symm

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) (v : V n) : A.loc (c • α) i v = c • A.loc α i v := by
  unfold HolAtlas.loc; split_ifs
  · rfl
  · exact (smul_zero c).symm

theorem dens_add (x y : Alt n) : dens (x + y) = dens x + dens y := by
  simp only [dens, map_add, Finsupp.add_apply, add_div]

theorem dens_smul (c : ℂ) (x : Alt n) : dens (c • x) = c * dens x := by
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

theorem reDens_add (α β : A.Fld) (i : A.ι) (v : V n) :
    A.reDens (α + β) i v = A.reDens α i v + A.reDens β i v := by
  simp only [HolAtlas.reDens, loc_add, dens_add, Complex.add_re]

theorem reDens_smul (t : ℝ) (α : A.Fld) (i : A.ι) (v : V n) :
    A.reDens ((t : ℂ) • α) i v = t * A.reDens α i v := by
  simp only [HolAtlas.reDens, loc_smul, dens_smul, Complex.re_ofReal_mul]

variable [MeasurableSpace M]

def G (r : A.ι → V n → ℝ) : Measure M := glueMeas A.e fun i y => ENNReal.ofReal (r i (A.e i y))

def Good (r : A.ι → V n → ℝ) : Prop :=
  (∀ i, ContinuousOn (r i) (A.e i).target) ∧
  ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
    r i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y)

theorem part_eq (γ : A.Fld) (ε : ℤˣ) (r : A.ι → V n → ℝ) (h : ∀ i v, ((ε : ℤ) : ℝ) * A.reDens γ i v = r i v) :
    A.part γ ε = G A r := by
  simp only [HolAtlas.part, G]
  congr 1
  funext i y
  rw [← h]
  rfl

theorem good_lin {α : A.Fld} (hα : A.IsForm α) (c : ℝ) : Good A fun i v => c * A.reDens α i v :=
  ⟨fun i => continuousOn_const.mul (A.continuousOn_reDens hα i),
    fun i j y hi hj => by simp only [A.reDens_compat hα i j y hi hj]; ring⟩

theorem isJacobianCompatibleDensity_linearCombination_realDensity {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) (c d : ℝ) :
    Good A fun i v => c * A.reDens α i v + d * A.reDens β i v :=
  ⟨fun i => (continuousOn_const.mul (A.continuousOn_reDens hα i)).add
      (continuousOn_const.mul (A.continuousOn_reDens hβ i)),
    fun i j y hi hj => by simp only [A.reDens_compat hα i j y hi hj, A.reDens_compat hβ i j y hi hj]; ring⟩

theorem glueMeas_mono [BorelSpace M] {ρ ρ' : A.ι → M → ℝ≥0∞} (h : ∀ i y, ρ i y ≤ ρ' i y) :
    glueMeas A.e ρ ≤ glueMeas A.e ρ' := by
  unfold glueMeas
  exact iSup_mono fun i => Measure.le_iff.2 fun S hS => by
    rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
    exact lintegral_mono fun v => h i _

variable [BorelSpace M] [SecondCountableTopology M]

theorem aem {r : A.ι → V n → ℝ} (hr : Good A r) (i : A.ι) (S : Set M) :
    AEMeasurable (fun v => ENNReal.ofReal (r i (A.e i ((A.e i).symm v))))
      (volume.restrict ((A.e i).target ∩ (A.e i).symm ⁻¹' S)) :=
  (HolAtlas.aemeasurable_ofReal_chart (A.e i) (r i) (hr.1 i)).mono_measure
    (Measure.restrict_mono (inter_subset_inter_right _ (preimage_mono (subset_univ S))) le_rfl)

theorem G_add {r₁ r₂ : A.ι → V n → ℝ} (h₁ : Good A r₁) (h₂ : Good A r₂) :
    glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y))) = G A r₁ + G A r₂ := by
  ext S hS
  rw [Measure.add_apply]
  exact glueMeas_add_of_compat_on A.e A.holo A.cover hS _ _
    (fun i j y _ hi hj => A.ofReal_compat r₁ h₁.2 i j y hi hj)
    (fun i j y _ hi hj => A.ofReal_compat r₂ h₂.2 i j y hi hj) (fun i => aem A h₁ i S)

theorem holAtlasGluedDensityMeasure_add_three {r₁ r₂ r₃ : A.ι → V n → ℝ} (h₁ : Good A r₁) (h₂ : Good A r₂) (h₃ : Good A r₃) :
    glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)) +
      ENNReal.ofReal (r₃ i (A.e i y))) = G A r₁ + G A r₂ + G A r₃ := by
  ext S hS
  have c₁ := A.ofReal_compat r₁ h₁.2
  have c₂ := A.ofReal_compat r₂ h₂.2
  have c₃ := A.ofReal_compat r₃ h₃.2
  rw [Measure.add_apply, Measure.add_apply,
    glueMeas_add_of_compat_on A.e A.holo A.cover hS
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i y => ENNReal.ofReal (r₃ i (A.e i y)))
      (fun i j y _ hi hj => by rw [c₁ i j y hi hj, c₂ i j y hi hj, mul_add])
      (fun i j y _ hi hj => c₃ i j y hi hj)
      (fun i => (aem A h₁ i S).add (aem A h₂ i S)),
    glueMeas_add_of_compat_on A.e A.holo A.cover hS
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) (fun i y => ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i j y _ hi hj => c₁ i j y hi hj) (fun i j y _ hi hj => c₂ i j y hi hj)
      (fun i => aem A h₁ i S)]
  rfl

theorem G_smul {r : A.ι → V n → ℝ} (h : Good A r) {c : ℝ} (hc : 0 ≤ c) :
    G A (fun i v => c * r i v) = ENNReal.ofReal c • G A r := by
  have hc' : Good A (fun i v => c * r i v) :=
    ⟨fun i => continuousOn_const.mul (h.1 i), fun i j y hi hj => by simp only [h.2 i j y hi hj]; ring⟩
  refine ext_of_cover (fun i => (A.e i).source) (fun i => (A.e i).open_source) A.cover fun i S hS hSi => ?_
  rw [Measure.smul_apply, G, G, glueMeas_apply _ _ A.holo (fun i j y hi hj => A.ofReal_compat (fun i v => c * r i v) hc'.2 i j y hi hj) i hS hSi,
    glueMeas_apply _ _ A.holo (fun i j y hi hj => A.ofReal_compat _ h.2 i j y hi hj) i hS hSi,
    chartMeas_apply_of_subset _ _ hS hSi, chartMeas_apply_of_subset _ _ hS hSi, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun v => ?_
  rw [ENNReal.ofReal_mul hc]

theorem part_finite [CompactSpace M] {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) : IsFiniteMeasure (A.part α ε) := by
  have h := good_lin A hα ((ε : ℤ) : ℝ)
  have e : A.part α ε = G A (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) := part_eq A α ε _ fun _ _ => rfl
  have fin : G A (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) univ ≠ ∞ :=
    GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn A.e A.cover A.holo (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) h.1 h.2
  refine ⟨?_⟩
  rw [e]
  exact lt_top_iff_ne_top.2 fin

theorem part_add_le {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) (ε : ℤˣ) :
    A.part (α + β) ε ≤ A.part α ε + A.part β ε := by
  rw [part_eq A (α + β) ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v + ((ε : ℤ) : ℝ) * A.reDens β i v)
      fun i v => by rw [reDens_add, mul_add],
    part_eq A α ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    part_eq A β ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens β i v) fun _ _ => rfl,
    ← G_add A (good_lin A hα _) (good_lin A hβ _)]
  exact glueMeas_mono A fun i y => ENNReal.ofReal_add_le

theorem part_balance {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.part (α + β) 1 + A.part α (-1) + A.part β (-1) = A.part (α + β) (-1) + A.part α 1 + A.part β 1 := by
  rw [part_eq A (α + β) 1 (fun i v => 1 * A.reDens α i v + 1 * A.reDens β i v)
      fun i v => by simp [reDens_add],
    part_eq A α (-1) (fun i v => (-1) * A.reDens α i v + 0 * A.reDens β i v) fun i v => by simp,
    part_eq A β (-1) (fun i v => 0 * A.reDens α i v + (-1) * A.reDens β i v) fun i v => by simp,
    part_eq A (α + β) (-1) (fun i v => (-1) * A.reDens α i v + (-1) * A.reDens β i v)
      fun i v => by simp [reDens_add]; ring,
    part_eq A α 1 (fun i v => 1 * A.reDens α i v + 0 * A.reDens β i v) fun i v => by simp,
    part_eq A β 1 (fun i v => 0 * A.reDens α i v + 1 * A.reDens β i v) fun i v => by simp,
    ← holAtlasGluedDensityMeasure_add_three A (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _),
    ← holAtlasGluedDensityMeasure_add_three A (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _)]
  congr 1
  funext i y
  have := HolAtlas.ofReal_posNeg (A.reDens α i (A.e i y)) (-A.reDens β i (A.e i y))
  convert this using 3 <;> ring_nf

theorem part_smul_nonneg {α : A.Fld} (hα : A.IsForm α) {t : ℝ} (ht : 0 ≤ t) (ε : ℤˣ) :
    A.part ((t : ℂ) • α) ε = ENNReal.ofReal t • A.part α ε := by
  rw [part_eq A ((t : ℂ) • α) ε (fun i v => t * (((ε : ℤ) : ℝ) * A.reDens α i v))
      fun i v => by rw [reDens_smul]; ring,
    part_eq A α ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    G_smul A (good_lin A hα _) ht]

theorem part_smul_nonpos {α : A.Fld} (hα : A.IsForm α) {t : ℝ} (ht : t ≤ 0) (ε : ℤˣ) :
    A.part ((t : ℂ) • α) ε = ENNReal.ofReal (-t) • A.part α (-ε) := by
  rw [part_eq A ((t : ℂ) • α) ε (fun i v => (-t) * ((((-ε : ℤˣ) : ℤ) : ℝ) * A.reDens α i v))
      fun i v => by rw [reDens_smul, Units.val_neg, Int.cast_neg]; ring,
    part_eq A α (-ε) (fun i v => (((-ε : ℤˣ) : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    G_smul A (good_lin A hα _) (neg_nonneg.2 ht)]

theorem part_congr {α β : A.Fld} (h : ∀ x, dens (α x) = dens (β x)) (ε : ℤˣ) : A.part α ε = A.part β ε := by
  simp only [HolAtlas.part]
  congr 1
  funext i y
  congr 3
  unfold HolAtlas.loc
  split_ifs
  · exact h _
  · rfl

end GlobalTheory.LineForm.TopInt

namespace GlobalTheory.LineForm

open GlobalTheory.LineForm.TopInt

theorem wInt_props : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    (∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, IsFiniteMeasure (A.part α ε)) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), A.IsForm α → A.IsForm β → (∀ ε : ℤˣ, Integrable g (A.part α ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part β ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part (α + β) ε)) ∧ wInt A g (α + β) = wInt A g α + wInt A g β) ∧
    (∀ (g : M → ℝ) (t : ℝ) (α : A.Fld), A.IsForm α → wInt A g ((t : ℂ) • α) = t * wInt A g α) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), (∀ x, dens (α x) = dens (β x)) → wInt A g α = wInt A g β) := by
  intro M _ _ _ _ _ _ n A
  refine ⟨fun α hα ε => part_finite A hα ε, fun g α β hα hβ ga gb => ?_, fun g t α hα => ?_,
    fun g α β h => by simp only [wInt, part_congr A h]⟩
  · have gs : ∀ ε : ℤˣ, Integrable g (A.part (α + β) ε) := fun ε =>
      ((ga ε).add_measure (gb ε)).mono_measure (part_add_le A hα hβ ε)
    refine ⟨gs, ?_⟩
    have key := congrArg (fun μ : Measure M => ∫ y, g y ∂μ) (part_balance A hα hβ)
    rw [integral_add_measure (((gs 1).add_measure (ga (-1)))) (gb (-1)),
      integral_add_measure (gs 1) (ga (-1)),
      integral_add_measure (((gs (-1)).add_measure (ga 1))) (gb 1),
      integral_add_measure (gs (-1)) (ga 1)] at key
    simp only [wInt]
    linarith
  · rcases le_total 0 t with ht | ht
    · simp only [wInt, part_smul_nonneg A hα ht, integral_smul_measure, ENNReal.toReal_ofReal ht, smul_eq_mul]
      ring
    · simp only [wInt, part_smul_nonpos A hα ht, integral_smul_measure, ENNReal.toReal_ofReal (neg_nonneg.2 ht),
        smul_eq_mul, neg_neg]
      ring

end GlobalTheory.LineForm
