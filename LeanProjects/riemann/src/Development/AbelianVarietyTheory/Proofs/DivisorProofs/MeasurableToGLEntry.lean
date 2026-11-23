import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace GlobalTheory.JSW

variable {n : ℕ}

def htGL (g : GL (Fin n) ℂ) : ℝ :=
  1 + ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ + ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖

def IsModGrowth (W : GL (Fin n) ℂ → ℂ) : Prop :=
  Continuous W ∧ ∃ (C : ℝ) (N : ℕ), ∀ g, ‖W g‖ ≤ C * htGL g ^ N

def IsRapid {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin n) ℂ) : Prop :=
  Measurable k ∧ (∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) ℂ) i j) ∧
    ∀ N : ℕ, Integrable (fun x => ‖k x‖ * htGL (γ x) ^ N) ν

def IsRapidF {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (ν : Measure X) (k : X → ℂ)
    (γ : X → GL (Fin n) ℂ) (η : X → Z →L[ℝ] ℝ) : Prop :=
  Measurable k ∧ (∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) ℂ) i j) ∧ (∀ z, Measurable fun x => η x z) ∧
    ∀ N : ℕ, Integrable (fun x => ‖k x‖ * (htGL (γ x) * (1 + ‖η x‖)) ^ N) ν

def IsKerOp {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : (GL (Fin n) ℂ → ℂ) → Z → GL (Fin n) ℂ → ℂ) : Prop :=
  ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin n) ℂ)
    (η : X → Z →L[ℝ] ℝ), IsRapidF ν k γ η ∧
      ∀ W, IsModGrowth W → ∀ z g, T W z g = ∫ x, k x * (𝐞 (η x z) : ℂ) * W (g * γ x) ∂ν

def levSet (n r : ℕ) : Set (GL (Fin n) ℂ) :=
  {g | ∀ i : Fin n, r ≤ (i : ℕ) → (∀ j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
    (g : Matrix (Fin n) (Fin n) ℂ) i i = 1}

def rowCut (ρ : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℂ := fun j => if j ≤ ρ then x ρ j else 0

def secMat (ρ j : Fin n) (v : Fin n → ℂ) : Fin n → Fin n → ℂ :=
  fun i l => if i = ρ then (if l ≤ ρ then v l else 0) else if l = Equiv.swap j ρ i then 1 else 0

def smoothMat (α : (Fin n → Fin n → ℂ) → ℂ) (W : GL (Fin n) ℂ → ℂ) (g : GL (Fin n) ℂ) : ℂ :=
  ∫ a : Fin n → Fin n → ℂ, α a * onMat W ((g : Matrix (Fin n) (Fin n) ℂ) * Matrix.of a)

open Classical in

def toGL (x : Matrix (Fin n) (Fin n) ℂ) : GL (Fin n) ℂ := if h : IsUnit x then h.unit else 1

theorem val_toGL {x : Matrix (Fin n) (Fin n) ℂ} (h : IsUnit x) : (toGL x : Matrix (Fin n) (Fin n) ℂ) = x := by
  simp [toGL, h]

theorem one_le_htGL (g : GL (Fin n) ℂ) : 1 ≤ htGL g := by
  unfold htGL
  have h1 : 0 ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have h2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  linarith

theorem htGL_pos (g : GL (Fin n) ℂ) : 0 < htGL g := lt_of_lt_of_le one_pos (one_le_htGL g)

theorem htGL_inv (g : GL (Fin n) ℂ) : htGL g⁻¹ = htGL g := by
  unfold htGL; rw [inv_inv]; ring

theorem sum_norm_mul_le (a b : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, ‖(a * b) i j‖ ≤ (∑ i, ∑ j, ‖a i j‖) * ∑ i, ∑ j, ‖b i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(a * b) i j‖ ≤ ∑ j, ∑ l, ‖a i l‖ * ‖b l j‖ :=
        Finset.sum_le_sum fun j _ => by
          rw [Matrix.mul_apply]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_mul_le _ _)
    _ = ∑ l, ‖a i l‖ * ∑ j, ‖b l j‖ := by rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ ≤ ∑ l, ‖a i l‖ * ∑ l', ∑ j, ‖b l' j‖ :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun l' => ∑ j, ‖b l' j‖) (fun _ _ => by positivity) (Finset.mem_univ l))
          (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem htGL_mul_le (g h : GL (Fin n) ℂ) : htGL (g * h) ≤ htGL g * htGL h := by
  unfold htGL
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  have h1 := sum_norm_mul_le (g : Matrix (Fin n) (Fin n) ℂ) h
  have h2 := sum_norm_mul_le ((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (g⁻¹ : GL (Fin n) ℂ)
  have a1 : 0 ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a3 : 0 ≤ ∑ i, ∑ j, ‖(h : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have a4 : 0 ≤ ∑ i, ∑ j, ‖((h⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  nlinarith [mul_nonneg a1 a4, mul_nonneg a2 a3]

theorem norm_entry_le_htGL (g : GL (Fin n) ℂ) (i j : Fin n) : ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ htGL g := by
  unfold htGL
  have h2 : 0 ≤ ∑ i, ∑ j, ‖((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j‖ := by positivity
  have h1 : ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ∑ i, ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖ :=
    (Finset.single_le_sum (f := fun j => ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖) (fun _ _ => by positivity)
      (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖(g : Matrix (Fin n) (Fin n) ℂ) i j‖) (fun _ _ => by positivity)
      (Finset.mem_univ i))
  linarith

theorem continuous_htGL : Continuous (htGL : GL (Fin n) ℂ → ℝ) := by
  have h1 : Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) := Units.continuous_val
  have h2 : Continuous fun g : GL (Fin n) ℂ => ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    Units.continuous_coe_inv
  unfold htGL
  fun_prop

theorem isOpenEmbedding_valGL :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) ℂ => fun i j => (g : Matrix (Fin n) (Fin n) ℂ) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) ℂ)

theorem measurable_comp_GL {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) ℂ → β} (hF : Continuous F) {γ : X → GL (Fin n) ℂ}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) ℂ) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) ℂ) := borel _
  haveI : BorelSpace (GL (Fin n) ℂ) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_valGL.measurableEmbedding.measurable_comp_iff).1
    (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hγ i j)
  exact hF.measurable.comp h

theorem measurable_dual {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] {η : X → Z →L[ℝ] ℝ} (h : ∀ z, Measurable fun x => η x z) : Measurable η := by
  let b := Module.finBasis ℝ Z
  have : η = fun x => ∑ i, η x (b i) • LinearMap.toContinuousLinearMap (b.coord i) := by
    funext x
    ext z
    conv_lhs => rw [← b.sum_repr z, map_sum]
    simp only [map_smul]
    simp [mul_comm]
  rw [this]
  exact Finset.measurable_sum _ fun i _ => (h _).smul_const _

theorem IsRapidF.integrable {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {ν : Measure X}
    {k : X → ℂ} {γ : X → GL (Fin n) ℂ} {η : X → Z →L[ℝ] ℝ} (h : IsRapidF ν k γ η) {W : GL (Fin n) ℂ → ℂ}
    (hW : IsModGrowth W) (z : Z) (g : GL (Fin n) ℂ) :
    Integrable (fun x => k x * (𝐞 (η x z) : ℂ) * W (g * γ x)) ν := by
  obtain ⟨hc, C, N, hC⟩ := hW
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (pow_pos (htGL_pos _) _)
  refine ((h.2.2.2 N).const_mul (C * htGL g ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine Measurable.aestronglyMeasurable ((h.1.mul ?_).mul ?_)
    · exact (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp (h.2.2.1 z)
    · exact measurable_comp_GL (F := fun q => W (g * q)) (by fun_prop) h.2.1
  · rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    have h1 : htGL (g * γ x) ≤ htGL g * (htGL (γ x) * (1 + ‖η x‖)) :=
      (htGL_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (htGL_pos _).le (by linarith [norm_nonneg (η x)])) (htGL_pos _).le)
    have h2 := pow_le_pow_left₀ (htGL_pos _).le h1 N
    rw [mul_pow] at h2
    calc ‖k x‖ * ‖W (g * γ x)‖ ≤ ‖k x‖ * (C * (htGL g ^ N * (htGL (γ x) * (1 + ‖η x‖)) ^ N)) :=
          mul_le_mul_of_nonneg_left ((hC _).trans (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _)
      _ = _ := by ring

def IsRapidFam {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (ν : Measure X)
    (k : GL (Fin n) ℂ → X → ℂ) (γ : X → GL (Fin n) ℂ) (η : GL (Fin n) ℂ → X → Z →L[ℝ] ℝ) : Prop :=
  (∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) ℂ) i j) ∧
  (∀ (X₀ : Type) [MeasurableSpace X₀] (γ₀ : X₀ → GL (Fin n) ℂ),
    (∀ i j, Measurable fun x => (γ₀ x : Matrix (Fin n) (Fin n) ℂ) i j) →
      Measurable (fun p : X₀ × X => k (γ₀ p.1) p.2) ∧ ∀ z, Measurable fun p : X₀ × X => η (γ₀ p.1) p.2 z) ∧
  ∀ N : ℕ, ∃ (C : ℝ) (M : ℕ), ∀ q, Integrable (fun x => ‖k q x‖ * (htGL (γ x) * (1 + ‖η q x‖)) ^ N) ν ∧
    ∫ x, ‖k q x‖ * (htGL (γ x) * (1 + ‖η q x‖)) ^ N ∂ν ≤ C * htGL q ^ M

def sandCLM (A B : Matrix (Fin n) (Fin n) ℂ) : (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i j => (A * Matrix.of x * B) i j
      map_add' := fun x y => by
        funext i j
        change (A * (Matrix.of x + Matrix.of y) * B) i j = (A * Matrix.of x * B) i j + (A * Matrix.of y * B) i j
        rw [mul_add, add_mul, Matrix.add_apply]
      map_smul' := fun c x => by
        funext i j
        change (A * (c • Matrix.of x) * B) i j = c • (A * Matrix.of x * B) i j
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] }

open Classical in

def secK {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (R : ℝ) (σ₀ : Fin n → Fin n → ℂ) (κ : X → ℂ)
    (τ : X → (Z × (Fin n → Fin n → ℂ)) →L[ℝ] ℝ) (q : GL (Fin n) ℂ) (p : (Fin n → Fin n → ℂ) × X) : ℂ :=
  if IsUnit (Matrix.of p.1) ∧ htGL (toGL (Matrix.of p.1)) ≤ R * htGL q then
    ((Complex.normSq ((q⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ n : ℝ) : ℂ) * κ p.2 *
      (𝐞 (τ p.2 (0, sandCLM ((q⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (Matrix.of p.1) σ₀)) : ℂ)
  else 0

def secEta {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : Z →L[ℝ] (Fin n → Fin n → ℂ))
    (τ : X → (Z × (Fin n → Fin n → ℂ)) →L[ℝ] ℝ) (q : GL (Fin n) ℂ) (p : (Fin n → Fin n → ℂ) × X) : Z →L[ℝ] ℝ :=
  (τ p.2).comp ((ContinuousLinearMap.id ℝ Z).prod
    ((sandCLM ((q⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (Matrix.of p.1)).comp L))

def IsWhitEq (ψ : AddChar ℂ ℂ) (W : GL (Fin n) ℂ → ℂ) : Prop :=
  ∀ u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g

end GlobalTheory.JSW
