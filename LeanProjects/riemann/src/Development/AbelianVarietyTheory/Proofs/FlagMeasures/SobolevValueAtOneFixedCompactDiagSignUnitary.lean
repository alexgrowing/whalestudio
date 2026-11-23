import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevInequalityAtOneIndefiniteUnitary

open MeasureTheory Matrix Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.SobolevHaar

theorem ofReal_list_sum_le {α : Type} (S : List α) (f : α → ℝ) :
    ENNReal.ofReal (S.map f).sum ≤ (S.map fun a => ENNReal.ofReal (f a)).sum := by
  induction S with
  | nil => simp
  | cons a S ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

private theorem ofReal_integral_le_lintegral_ofReal {X : Type} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf)).le
  · rw [integral_undef hi]
    simp

theorem sobolev_at_one_compact : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ) (Q : Set (Formalism.REAL.UJ ε)), IsCompact Q ∧ (∀ l ∈ S, ∀ X ∈ l, Formalism.REAL.inG ε X) ∧ 0 ≤ C ∧ ∀ F : List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ContinuousOn (F l) (UJset ε)) → (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ X, Formalism.REAL.inG ε X → ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) (F (X :: l) g) 0) → ENNReal.ofReal (‖F [] 1‖ ^ 2) ≤ ENNReal.ofReal C * (S.map fun l => ∫⁻ y in Q, ENNReal.ofReal (‖F l (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
  intro n ε

  obtain ⟨E, hE, hON, -⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  obtain ⟨s, hs, hsmall⟩ := exists_small n
  obtain ⟨c, -, hc, -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge n ε
  have hEl : ∀ i, E i ∈ GlobalTheory.GaugeConst.lieJ ε := fun i => GlobalTheory.GaugeConst.mem_lieJ.2 (hE i).1
  have hsm : ∀ (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ), (t : ℂ) • X = t • X := by
    intro t X
    ext a b
    simp [Complex.real_smul]

  obtain ⟨cu, hcuM, hcuc⟩ : ∃ cu : Fin (n ^ 2) → ℝ → Formalism.REAL.UJ ε,
      (∀ i t, umat (cu i t) = NormedSpace.exp ((t : ℂ) • E i)) ∧ ∀ i, Continuous (cu i) := by
    refine ⟨fun i t => GlobalTheory.GaugeConst.expJ ε (t • ⟨E i, hEl i⟩), fun i t => ?_, fun i => ?_⟩
    · rw [hsm]
      exact GlobalTheory.GaugeConst.uMat_expJ ε (t • ⟨E i, hEl i⟩)
    · exact (GlobalTheory.GaugeConst.continuous_expJ ε).comp (continuous_id.smul continuous_const)
  have hu1 : umat (1 : Formalism.REAL.UJ ε) = 1 := rfl
  have humul : ∀ x y : Formalism.REAL.UJ ε, umat (x * y) = umat x * umat y := fun _ _ => rfl
  have hinj : Function.Injective (fun x : Formalism.REAL.UJ ε => umat x) :=
    GlobalTheory.GaugeConst.uMat_injective ε
  have hcu0 : ∀ i, cu i 0 = 1 := by
    intro i
    apply hinj
    show umat (cu i 0) = umat 1
    rw [hcuM, hu1]
    simp
  have hcuadd : ∀ i a b, cu i (a + b) = cu i a * cu i b := by
    intro i a b
    apply hinj
    show umat (cu i (a + b)) = umat (cu i a * cu i b)
    rw [humul, hcuM, hcuM, hcuM, Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl (E i)).smul_left _).smul_right _)

  have hlist : ∀ l : List (Formalism.REAL.UJ ε), umat l.prod = (l.map fun x => umat x).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.prod_cons, humul, ih, List.map_cons, List.prod_cons]
  have hΘ : ∀ t : Fin (n ^ 2) → ℝ, umat ((List.ofFn fun i => cu i (t i)).prod) =
      (List.ofFn fun i => NormedSpace.exp ((t i : ℂ) • E i)).prod := by
    intro t
    rw [hlist, List.map_ofFn]
    simp only [Function.comp_def, hcuM]
  have hΘc : Continuous fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod :=
    GlobalTheory.continuous_prod_ofFn_curves (n ^ 2) cu hcuc
  obtain ⟨K, hchart⟩ : ∃ K : ℝ, ∀ Φ : Formalism.REAL.UJ ε → ENNReal, Measurable Φ →
      ∫⁻ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          Φ ((List.ofFn fun i => cu i (t i)).prod) ≤
        ENNReal.ofReal K * ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
          Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s), Φ y ∂(Formalism.REAL.muG ε) :=
    ⟨_, GlobalTheory.ProductChart.lintegral_chart_le n ε c s E
      (fun t => (List.ofFn fun i => cu i (t i)).prod) hc (fun i => (hE i).1) hON hs hsmall hΘ⟩

  have hD : ∀ i, ∀ v ∈ {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y},
      E i :: v ∈ {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y} := by
    intro i v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    · exact (hE i).1
    · exact hv Y hY
  obtain ⟨S, C0, hSA, hC0, hbound⟩ :=
    cube_sum {l : List (Matrix (Fin n) (Fin n) ℂ) | ∀ Y ∈ l, Formalism.REAL.inG ε Y} [] (by simp) s hs
      (n ^ 2) cu (fun i v => E i :: v) (fun i => ⟨hcuc i, hcu0 i, hcuadd i⟩) hD
  refine ⟨S, C0 * max K 0,
    (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
      Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
    (isCompact_univ_pi fun _ => isCompact_Icc).image hΘc,
    fun l hl => (hSA l hl : ∀ Y ∈ l, Formalism.REAL.inG ε Y),
    mul_nonneg hC0 (le_max_right _ _), ?_⟩
  intro F hFc hFd
  have hmem : ∀ x : Formalism.REAL.UJ ε, umat x ∈ UJset ε := fun x => x.2
  have hFrc : ∀ v : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ v, Formalism.REAL.inG ε Y) →
      Continuous fun x : Formalism.REAL.UJ ε => F v (umat x) := fun v hv =>
    (hFc v hv).comp_continuous (GlobalTheory.GaugeConst.continuous_uMat ε) hmem
  have hFrd : ∀ v : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ v, Formalism.REAL.inG ε Y) →
      ∀ (i : Fin (n ^ 2)) (x : Formalism.REAL.UJ ε),
        HasDerivAt (fun t => F v (umat (x * cu i t))) (F (E i :: v) (umat x)) 0 := by
    intro v hv i x
    have h := hFd v hv (E i) (hE i).1 (umat x) (hmem x)
    have he : (fun t : ℝ => F v (umat (x * cu i t))) =
        fun t : ℝ => F v (umat x * NormedSpace.exp ((t : ℂ) • E i)) := by
      funext t
      rw [humul, hcuM]
    rw [he]
    exact h
  have hb : ‖F [] 1‖ ^ 2 ≤ C0 * (S.map fun v =>
      ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum :=
    hbound (fun v x => F v (umat x)) hFrc hFrd
  have hpt : ∀ v ∈ S,
      ENNReal.ofReal (∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2) ≤
      ENNReal.ofReal K * ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
          Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
        ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε) := by
    intro v hv
    have hcont := hFrc v (hSA v hv)
    have hmeas : Measurable fun y : Formalism.REAL.UJ ε => ENNReal.ofReal (‖F v (umat y)‖ ^ 2) :=
      (ENNReal.continuous_ofReal.comp (hcont.norm.pow 2)).measurable
    have h1 := ofReal_integral_le_lintegral_ofReal
      (volume.restrict (Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s)))
      (fun t => ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2) (fun t => sq_nonneg _)
    have h2 := hchart (fun y => ENNReal.ofReal (‖F v (umat y)‖ ^ 2)) hmeas
    exact h1.trans h2
  calc ENNReal.ofReal (‖F [] 1‖ ^ 2)
      ≤ ENNReal.ofReal (C0 * (S.map fun v =>
          ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
            ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum) :=
        ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal C0 * ENNReal.ofReal (S.map fun v =>
          ∫ t in Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
            ‖F v (umat ((List.ofFn fun i => cu i (t i)).prod))‖ ^ 2).sum :=
        ENNReal.ofReal_mul hC0
    _ ≤ ENNReal.ofReal C0 * (S.map fun v => ENNReal.ofReal K *
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        gcongr
        exact (ofReal_list_sum_le _ _).trans (List.sum_le_sum hpt)
    _ = ENNReal.ofReal C0 * ENNReal.ofReal K * (S.map fun v =>
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        rw [List.sum_map_mul_left, mul_assoc]
    _ ≤ ENNReal.ofReal (C0 * max K 0) * (S.map fun v =>
          ∫⁻ y in (fun t : Fin (n ^ 2) → ℝ => (List.ofFn fun i => cu i (t i)).prod) ''
            Set.pi Set.univ (fun _ : Fin (n ^ 2) => Set.Icc (0 : ℝ) s),
          ENNReal.ofReal (‖F v (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
        rw [ENNReal.ofReal_mul hC0]
        gcongr
        exact le_max_left _ _

end GlobalTheory.SobolevHaar
