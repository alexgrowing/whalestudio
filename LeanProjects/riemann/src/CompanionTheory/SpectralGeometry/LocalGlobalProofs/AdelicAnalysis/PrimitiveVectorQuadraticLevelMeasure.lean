import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalHaarQuadraticSubstitutionInvariantStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardLocalHaarPropertiesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Hensel

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem mem_int {x : Fv F v} : x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := Iff.rfl

theorem v_le_of_close {x y : Fv F v} (hy : Valued.v y ≤ 1) (h : Valued.v (x - y) < 1) :
    Valued.v x ≤ 1 := by
  have : x = (x - y) + y := by ring
  rw [this]
  exact (Valuation.map_add _ _ _).trans (max_le h.le hy)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mulVec_le {B : Matrix ι ι (Fv F v)} (hB : ∀ i j, Valued.v (B i j) ≤ 1)
    {x : ι → Fv F v} (hx : ∀ i, Valued.v (x i) ≤ 1) (k : ι) : Valued.v ((B *ᵥ x) k) ≤ 1 := by
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (hB k j) (hx j)

theorem mulVec_lt {B : Matrix ι ι (Fv F v)} (hB : ∀ i j, Valued.v (B i j) ≤ 1)
    {x : ι → Fv F v} (hx : ∀ i, Valued.v (x i) < 1) (k : ι) : Valued.v ((B *ᵥ x) k) < 1 := by
  refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hB k j)) (hx j)

theorem dot_close {B : Matrix ι ι (Fv F v)} (hB : ∀ i j, Valued.v (B i j) ≤ 1)
    {x y : ι → Fv F v} (hy : ∀ i, Valued.v (y i) ≤ 1) (h : ∀ i, Valued.v (x i - y i) < 1) :
    Valued.v (x ⬝ᵥ (B *ᵥ x) - y ⬝ᵥ (B *ᵥ y)) < 1 := by
  have hx : ∀ i, Valued.v (x i) ≤ 1 := fun i => v_le_of_close (hy i) (h i)
  have e : x ⬝ᵥ (B *ᵥ x) - y ⬝ᵥ (B *ᵥ y) = (x - y) ⬝ᵥ (B *ᵥ x) + y ⬝ᵥ (B *ᵥ (x - y)) := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]; ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ ?_
  · refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (mulVec_le hB hx j)) (h j)
  · refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hy j)) (mulVec_lt hB (x := x - y) h j)

theorem exists_unit_coord {B : Matrix ι ι (Fv F v)} (hB : ∀ i j, Valued.v (B i j) ≤ 1)
    (hdet : Valued.v B.det = 1) {x : ι → Fv F v} (hx : ∀ i, Valued.v (x i) ≤ 1)
    (hp : ∃ i, Valued.v (x i) = 1) : ∃ i, Valued.v ((B *ᵥ x) i) = 1 := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ i, Valued.v ((B *ᵥ x) i) < 1 := fun i =>
    lt_of_le_of_ne (mulVec_le hB hx i) (hcon i)
  obtain ⟨i, hi⟩ := hp
  let O := v.adicCompletionIntegers F
  let B' : Matrix ι ι O := fun a b => ⟨B a b, hB a b⟩
  have hmap : B = (O.subtype : O →+* Fv F v).mapMatrix B' := by
    ext a b; rfl
  have hadj : ∀ a b, Valued.v (B.adjugate a b) ≤ 1 := by
    intro a b
    rw [hmap, ← RingHom.map_adjugate]
    exact (B'.adjugate a b).2
  have h1 : (B.adjugate *ᵥ (B *ᵥ x)) i = B.det * x i := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp
  have h2 := mulVec_lt hadj hlt i
  rw [h1, map_mul, hdet, hi, one_mul] at h2
  exact lt_irrefl _ h2

theorem dot_add_single {B : Matrix ι ι (Fv F v)} (hs : B.IsSymm) (x : ι → Fv F v) (i : ι)
    (s : Fv F v) :
    (x + Pi.single i s) ⬝ᵥ (B *ᵥ (x + Pi.single i s)) =
      x ⬝ᵥ (B *ᵥ x) + 2 * (B *ᵥ x) i * s + B i i * s ^ 2 := by
  have hv : x ᵥ* B = B *ᵥ x := by
    conv_lhs => rw [← hs.eq]
    exact Matrix.vecMul_transpose B x
  have h1 : x ⬝ᵥ (B *ᵥ Pi.single i s) = (B *ᵥ x) i * s := by
    rw [Matrix.dotProduct_mulVec, hv, dotProduct_single]
  have h2 : (Pi.single i s : ι → Fv F v) ⬝ᵥ (B *ᵥ x) = (B *ᵥ x) i * s := by
    rw [single_dotProduct, mul_comm]
  have h3 : (Pi.single i s : ι → Fv F v) ⬝ᵥ (B *ᵥ Pi.single i s) = B i i * s ^ 2 := by
    rw [single_dotProduct]
    simp [Matrix.mulVec_single]
    ring
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, h1, h2, h3]
  ring

section Meas

variable {lam : Measure (Fv F v)}

theorem isOpen_maxIdeal : IsOpen {t : Fv F v | Valued.v t < 1} := by
  simpa using Valued.isOpen_ball (Fv F v) 1

theorem measurableSet_close (b : Fv F v) : MeasurableSet {t : Fv F v | Valued.v (t - b) < 1} := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact (isOpen_maxIdeal.preimage (continuous_sub_right b)).measurableSet

theorem slice (hstd : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1) {a c : Fv F v}
    (ha : Valued.v a = 1) (hc : c ∈ v.adicCompletionIntegers F) (q b : Fv F v)
    {A : Set (Fv F v)} (hA : MeasurableSet A) :
    lam {t | Valued.v (t - b) < 1 ∧ q + a * (t - b) + c * (t - b) ^ 2 ∈ A} =
      lam (A ∩ {s | Valued.v (s - q) < 1}) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨htop, hlc, hsc, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := hstd.1
  have hA' : MeasurableSet ((fun h => q + h) ⁻¹' A) := (measurable_const_add q) hA
  have key := GlobalTheory.T.local_haar_quadratic_substitution_invariant F v lam hstd h2 a c ha hc _ hA'
  have e1 : {t | Valued.v (t - b) < 1 ∧ q + a * (t - b) + c * (t - b) ^ 2 ∈ A} =
      (fun h => -b + h) ⁻¹' {t | Valued.v t < 1 ∧ a * t + c * t ^ 2 ∈ (fun h => q + h) ⁻¹' A} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, neg_add_eq_sub, add_assoc]
  have e2 : (fun h => q + h) ⁻¹' A ∩ {s | Valued.v s < 1} =
      (fun h => q + h) ⁻¹' (A ∩ {s | Valued.v (s - q) < 1}) := by
    ext t
    simp
  rw [e1, measure_preimage_add, key, e2, measure_preimage_add]

end Meas

section Main

variable {lam : Measure (Fv F v)}

theorem measurable_form (B : Matrix ι ι (Fv F v)) :
    Measurable fun x : ι → Fv F v => (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨htop, hlc, hsc, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have : Continuous fun x : ι → Fv F v => (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  exact this.measurable

theorem slice_form (hstd : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1)
    {B : Matrix ι ι (Fv F v)} (hs : B.IsSymm) (hB : ∀ i j, Valued.v (B i j) ≤ 1)
    {x₀ : ι → Fv F v} (hx₀ : ∀ i, Valued.v (x₀ i) ≤ 1) {i : ι}
    (hi : Valued.v ((B *ᵥ x₀) i) = 1) {A : Set (Fv F v)} (hA : MeasurableSet A)
    {x : ι → Fv F v} (hx : ∀ j, j ≠ i → Valued.v (x j - x₀ j) < 1) :
    lam {t | Function.update x i t ∈ {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
        (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ A}} =
      lam (A ∩ {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1}) := by
  set x' : ι → Fv F v := Function.update x i (x₀ i) with hx'def
  have hclose : ∀ j, Valued.v (x' j - x₀ j) < 1 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [x']
    · simpa [x', Function.update_of_ne hj] using hx j hj
  have h2ne : (2 : Fv F v) ≠ 0 := by
    intro h; rw [h, map_zero] at h2; exact zero_ne_one h2
  have hinv : Valued.v ((2 : Fv F v)⁻¹) = 1 := by rw [map_inv₀, h2, inv_one]
  have hupd : ∀ t, Function.update x i t = x' + Pi.single i (t - x₀ i) := by
    intro t
    ext j
    by_cases hj : j = i
    · subst hj; simp [x']
    · simp [x', Function.update_of_ne hj, Pi.single_eq_of_ne hj]
  have ha : Valued.v ((B *ᵥ x') i) = 1 := by
    have hd : Valued.v ((B *ᵥ x') i - (B *ᵥ x₀) i) < 1 := by
      have := mulVec_lt hB (x := x' - x₀) hclose i
      simpa [Matrix.mulVec_sub] using this
    have : (B *ᵥ x') i = (B *ᵥ x') i - (B *ᵥ x₀) i + (B *ᵥ x₀) i := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ (by rwa [hi]), hi]
  have hc : (2 : Fv F v)⁻¹ * B i i ∈ v.adicCompletionIntegers F := by
    rw [mem_int, map_mul, hinv, one_mul]; exact hB i i
  have hq : Valued.v ((2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1 := by
    rw [← mul_sub, map_mul, hinv, one_mul]
    exact dot_close hB hx₀ hclose
  have e1 : {t | Function.update x i t ∈ {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
        (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ A}} =
      {t | Valued.v (t - x₀ i) < 1 ∧ (2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) +
        (B *ᵥ x') i * (t - x₀ i) + ((2 : Fv F v)⁻¹ * B i i) * (t - x₀ i) ^ 2 ∈ A} := by
    ext t
    have hform : (2 : Fv F v)⁻¹ * (Function.update x i t ⬝ᵥ (B *ᵥ Function.update x i t)) =
        (2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) + (B *ᵥ x') i * (t - x₀ i) +
          ((2 : Fv F v)⁻¹ * B i i) * (t - x₀ i) ^ 2 := by
      rw [hupd t, dot_add_single hs]
      field_simp
    simp only [Set.mem_setOf_eq, hform]
    refine and_congr_left fun _ => ⟨fun h => by simpa using h i, fun h j => ?_⟩
    by_cases hj : j = i
    · subst hj; simpa using h
    · simpa [Function.update_of_ne hj] using hx j hj
  have e2 : {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x'))) < 1} =
      {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1} := by
    ext s
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have : s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀)) =
          (s - (2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x'))) +
            ((2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) := by ring
      rw [this]
      exact Valuation.map_add_lt _ h hq
    · intro h
      have : s - (2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) =
          (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) -
            ((2 : Fv F v)⁻¹ * (x' ⬝ᵥ (B *ᵥ x')) - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) := by ring
      rw [this]
      exact Valuation.map_sub_lt _ h hq
  rw [e1, slice hstd h2 ha hc _ _ hA, e2]

theorem pi_eq_mul [SigmaFinite lam] (i : ι) {S E : Set (ι → Fv F v)} (hS : MeasurableSet S)
    (hE : MeasurableSet E) (C : ℝ≥0∞) (hC : C ≠ ⊤) (x₀ : ι → Fv F v)
    (h1 : ∀ x, x ∈ E → lam {t | Function.update x i t ∈ S} = C)
    (h0 : ∀ x, x ∉ E → lam {t | Function.update x i t ∈ S} = 0) :
    (Measure.pi fun _ : ι => lam) S =
      C * (∫⋯∫⁻_(Finset.univ.erase i), E.indicator 1 ∂(fun _ : ι => lam)) x₀ := by
  have hf : Measurable (S.indicator (1 : (ι → Fv F v) → ℝ≥0∞)) := measurable_one.indicator hS
  have hg : Measurable (E.indicator (1 : (ι → Fv F v) → ℝ≥0∞)) := measurable_one.indicator hE
  have hU : (Finset.univ : Finset ι) = Finset.univ.erase i ∪ {i} := by
    ext j; by_cases hj : j = i <;> simp [hj]
  have hdis : Disjoint (Finset.univ.erase i) ({i} : Finset ι) := by simp
  have hin : (∫⋯∫⁻_{i}, S.indicator 1 ∂(fun _ : ι => lam)) =
      fun x => C * E.indicator (1 : (ι → Fv F v) → ℝ≥0∞) x := by
    rw [lmarginal_singleton]
    ext x
    have hsl : ∫⁻ t, S.indicator (1 : (ι → Fv F v) → ℝ≥0∞) (Function.update x i t) ∂lam =
        lam {t | Function.update x i t ∈ S} := by
      have hm : MeasurableSet {t | Function.update x i t ∈ S} := measurable_update x hS
      rw [← lintegral_indicator_one hm]
      refine lintegral_congr fun t => ?_
      by_cases ht : Function.update x i t ∈ S
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ {t | Function.update x i t ∈ S} from ht)]
        rfl
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show t ∉ {t | Function.update x i t ∈ S} from ht)]
    rw [hsl]
    by_cases hx : x ∈ E
    · simp [h1 x hx, hx]
    · simp [h0 x hx, hx]
  calc (Measure.pi fun _ : ι => lam) S
      = ∫⁻ x, S.indicator 1 x ∂(Measure.pi fun _ : ι => lam) := (lintegral_indicator_one hS).symm
    _ = (∫⋯∫⁻_Finset.univ, S.indicator 1 ∂(fun _ : ι => lam)) x₀ := lintegral_eq_lmarginal_univ x₀
    _ = (∫⋯∫⁻_(Finset.univ.erase i), (∫⋯∫⁻_{i}, S.indicator 1 ∂(fun _ : ι => lam))
          ∂(fun _ : ι => lam)) x₀ := by
        rw [← lmarginal_union _ _ hf hdis, ← hU]
    _ = C * (∫⋯∫⁻_(Finset.univ.erase i), E.indicator 1 ∂(fun _ : ι => lam)) x₀ := by
        rw [hin]
        exact lintegral_const_mul C (hg.comp measurable_updateFinset)

end Main

end SlopeTestRemainingChoices

theorem measure_residue_class : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ x₀ : ι → Fv F v, (∀ i, x₀ i ∈ v.adicCompletionIntegers F) → (∃ i, Valued.v (x₀ i) = 1) → ∀ A : Set (Fv F v), MeasurableSet A → (Measure.pi fun _ : ι => lam) {x | (∀ i, Valued.v (x i - x₀ i) < 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (Fintype.card ι - 1) * lam (A ∩ {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1}) := by
  intro F _ _ v lam hstd h2 ι _ _ B hs hB hdet x₀ hx₀ hp A hA
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨htop, hlc, hsc, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := hstd.1
  have hB' : ∀ i j, Valued.v (B i j) ≤ 1 := hB
  have hx₀' : ∀ i, Valued.v (x₀ i) ≤ 1 := hx₀
  obtain ⟨i, hi⟩ := exists_unit_coord hB' hdet hx₀' hp
  set Nn : ℝ≥0∞ := (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ with hNn
  have hvol : lam {t | Valued.v t < 1} = Nn := (GlobalTheory.T.standard_local_haar_properties F v lam hstd).1
  have hball : ∀ b : Fv F v, lam {s | Valued.v (s - b) < 1} = Nn := by
    intro b
    have : {s | Valued.v (s - b) < 1} = (fun h => -b + h) ⁻¹' {t | Valued.v t < 1} := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_preimage, neg_add_eq_sub]
    rw [this, measure_preimage_add, hvol]
  have hN0 : Nn ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hNt : Nn ≠ ⊤ := by
    rw [← hvol]
    refine ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top ?_
    rw [← hstd.2]
    exact measure_mono fun t ht => show t ∈ v.adicCompletionIntegers F from mem_int.2 (le_of_lt ht)
  set E : Set (ι → Fv F v) := {x | ∀ j, j ≠ i → Valued.v (x j - x₀ j) < 1} with hEdef
  have hsec : ∀ j, MeasurableSet {y : ι → Fv F v | Valued.v (y j - x₀ j) < 1} := fun j =>
    (measurable_pi_apply (X := fun _ : ι => Fv F v) j) (measurableSet_close (x₀ j))
  have hE : MeasurableSet E := by
    simp only [hEdef, Set.setOf_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => hsec j
  have hD : MeasurableSet {y : ι → Fv F v | ∀ j, Valued.v (y j - x₀ j) < 1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter hsec
  have hform : ∀ A' : Set (Fv F v), MeasurableSet A' →
      (Measure.pi fun _ : ι => lam) {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
          (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ A'} =
        lam (A' ∩ {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1}) *
          (∫⋯∫⁻_(Finset.univ.erase i), E.indicator 1 ∂(fun _ : ι => lam)) x₀ := by
    intro A' hA'
    have hS : MeasurableSet {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
        (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ A'} :=
      hD.inter ((measurable_form B) hA')
    refine pi_eq_mul i hS hE _ ?_ x₀ ?_ ?_
    · refine ne_top_of_le_ne_top hNt ?_
      rw [← hball ((2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀)))]
      exact measure_mono Set.inter_subset_right
    · intro x hx
      exact slice_form hstd h2 hs hB' hx₀' hi hA' hx
    · intro x hx
      simp only [hEdef, Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨j, hj, hjx⟩ := hx
      have : {t | Function.update x i t ∈ {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
          (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ A'}} = ∅ := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h
        exact absurd (by simpa [Function.update_of_ne hj] using h j) hjx
      rw [this, measure_empty]
  have hpi : (Measure.pi fun _ : ι => lam) {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
      (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ Set.univ} = Nn ^ Fintype.card ι := by
    have : {y : ι → Fv F v | (∀ j, Valued.v (y j - x₀ j) < 1) ∧
        (2 : Fv F v)⁻¹ * (y ⬝ᵥ (B *ᵥ y)) ∈ Set.univ} =
        Set.univ.pi fun j => {t | Valued.v (t - x₀ j) < 1} := by
      ext y
      simp
    rw [this, Measure.pi_pi]
    simp [hball]
  have hW : (∫⋯∫⁻_(Finset.univ.erase i), E.indicator 1 ∂(fun _ : ι => lam)) x₀ =
      Nn ^ (Fintype.card ι - 1) := by
    have h := hform Set.univ MeasurableSet.univ
    rw [hpi, Set.univ_inter, hball] at h
    have hcard : Fintype.card ι = (Fintype.card ι - 1) + 1 :=
      (Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨i⟩)).symm
    rw [hcard, pow_succ'] at h
    exact ((ENNReal.mul_right_inj hN0 hNt).mp h).symm
  rw [hform A hA, hW, mul_comm]

end GlobalTheory.CompanionTheory.SW.Hensel
