import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial MeasureTheory
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

namespace GlobalTheory.ChernScale

section General

variable {α : Type*} [MeasurableSpace α] {κ : Sort*}

theorem restrict_iSup_eq (μ : κ → Measure α) {S : Set α} (hS : MeasurableSet S) :
    (⨆ i, μ i).restrict S = ⨆ i, (μ i).restrict S := by
  refine le_antisymm ?_ (iSup_le fun i => Measure.restrict_mono subset_rfl (le_iSup μ i))
  have h : (⨆ i, μ i) ≤ (⨆ i, (μ i).restrict S) + (⨆ i, μ i).restrict Sᶜ := by
    refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
    rw [← Measure.restrict_add_restrict_compl (μ := μ i) hS, Measure.add_apply, Measure.add_apply]
    exact add_le_add (Measure.le_iff'.1 (le_iSup (fun i => (μ i).restrict S) i) B)
      (Measure.le_iff'.1 (Measure.restrict_mono subset_rfl (le_iSup μ i)) B)
  calc (⨆ i, μ i).restrict S ≤ ((⨆ i, (μ i).restrict S) + (⨆ i, μ i).restrict Sᶜ).restrict S :=
        Measure.restrict_mono subset_rfl h
    _ = (⨆ i, (μ i).restrict S).restrict S := by
        rw [Measure.restrict_add, Measure.restrict_restrict hS, Set.inter_compl_self,
          Measure.restrict_empty, add_zero]
    _ ≤ _ := Measure.restrict_le_self

theorem smul_iSup_eq (ν : κ → Measure α) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    c • (⨆ i, ν i) = ⨆ i, c • ν i := by
  have mono : ∀ (d : ℝ≥0∞) {μ μ' : Measure α}, μ ≤ μ' → d • μ ≤ d • μ' := fun d μ μ' h =>
    Measure.le_iff.2 fun s _ => by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl <| Measure.le_iff'.1 h s
  rcases eq_or_ne c 0 with rfl | h0
  · simp only [zero_smul]
    exact (le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)).symm
  refine le_antisymm ?_ (iSup_le fun i => mono c (le_iSup ν i))
  have key : (⨆ i, ν i) ≤ c⁻¹ • ⨆ i, c • ν i := iSup_le fun i => by
    calc ν i = c⁻¹ • c • ν i := by rw [smul_smul, ENNReal.inv_mul_cancel h0 hc, one_smul]
      _ ≤ _ := mono _ (le_iSup (fun i => c • ν i) i)
  calc c • (⨆ i, ν i) ≤ c • c⁻¹ • ⨆ i, c • ν i := mono c key
    _ = _ := by rw [smul_smul, ENNReal.mul_inv_cancel h0 hc, one_smul]

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {n : ℕ}

theorem chartMeas_restrict_eq (e : OpenPartialHomeomorph X (V n)) {ρ ρ' : X → ℝ≥0∞} {c : ℝ≥0∞}
    (hc : c ≠ ⊤) {S : Set X} (hS : MeasurableSet S) (h : ∀ y ∈ e.source, y ∈ S → ρ y = c * ρ' y) :
    (chartMeas e ρ).restrict S = c • (chartMeas e ρ').restrict S := by
  ext B hB
  rw [Measure.smul_apply, Measure.restrict_apply hB, Measure.restrict_apply hB, smul_eq_mul,
    chartMeas_apply e ρ (hB.inter hS), chartMeas_apply e ρ' (hB.inter hS), ← lintegral_const_mul' c _ hc]
  refine setLIntegral_congr_fun (measurableSet_image e (e.open_source.measurableSet.inter (hB.inter hS))
    Set.inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  show ρ (e.symm (e y)) = c * ρ' (e.symm (e y))
  rw [e.left_inv hy.1]
  exact h y hy.1 hy.2.2

theorem glueMeas_restrict_eq {ι : Type*} (e : ι → OpenPartialHomeomorph X (V n)) {ρ ρ' : ι → X → ℝ≥0∞}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) {S : Set X} (hS : MeasurableSet S)
    (h : ∀ i, ∀ y ∈ (e i).source, y ∈ S → ρ i y = c * ρ' i y) :
    (glueMeas e ρ).restrict S = c • (glueMeas e ρ').restrict S := by
  rw [glueMeas, glueMeas, restrict_iSup_eq _ hS, restrict_iSup_eq _ hS, smul_iSup_eq _ hc]
  exact iSup_congr fun i => chartMeas_restrict_eq (e i) hc hS (h i)

end General

end GlobalTheory.ChernScale

namespace GlobalTheory.GoodMetric

open GlobalTheory.ChernScale

theorem hasChernIntegral_of_eq_mul : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (R R₀ : MvPolynomial (ι × ℕ) ℝ) (t v : ℝ),
    (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∀ A ∈ E.S (under y),
      chernTop R (fun w => H A (c.e.symm w)) (c.e y) = t * chernTop R₀ (fun w => H A (c.e.symm w)) (c.e y)) →
    HasChernIntegral E O H R₀ v → HasChernIntegral E O H R (t * v) := by
  intro F _ σ X ι m E O H R R₀ t v hRt hv
  have hP : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  have key : ∀ (ε ε' : ℤˣ) (c : ℝ), 0 ≤ c → (∀ x : ℝ, ((ε : ℤ) : ℝ) * (t * x) = c * (((ε' : ℤ) : ℝ) * x)) →
      chernTopPart E H R ε (ptsIn X.str σ O) =
        ENNReal.ofReal c * chernTopPart E H R₀ ε' (ptsIn X.str σ O) := by
    intro ε ε' c hc hx
    have hm : (chernTopPart E H R ε).restrict (ptsIn X.str σ O) =
        ENNReal.ofReal c • (chernTopPart E H R₀ ε').restrict (ptsIn X.str σ O) :=
      glueMeas_restrict_eq _ ENNReal.ofReal_ne_top hP fun a y hy hyS => ?_
    · have := congrArg (fun μ : Measure (CxPts X.str σ) => μ (ptsIn X.str σ O)) hm
      simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_self] using this
    · have e1 := hRt y hyS a hy _ (E.nonempty (under y)).choose_spec
      beta_reduce
      rw [e1, hx, ENNReal.ofReal_mul hc]
  rcases le_or_gt 0 t with ht | ht
  · refine ⟨fun ε => ?_, ?_⟩
    · rw [key ε ε t ht (fun x => by ring)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv.1 ε)
    · rw [← hv.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def,
        key 1 1 t ht (fun x => by ring), key (-1) (-1) t ht (fun x => by ring),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
      ring
  · have ht' : 0 ≤ -t := by linarith
    refine ⟨fun ε => ?_, ?_⟩
    · rw [key ε (-ε) (-t) ht' (fun x => by rw [Units.val_neg, Int.cast_neg]; ring)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hv.1 _)
    · rw [← hv.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def,
        key 1 (-1) (-t) ht' (fun x => by push_cast; ring), key (-1) 1 (-t) ht' (fun x => by push_cast; ring),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht']
      ring

end GlobalTheory.GoodMetric
