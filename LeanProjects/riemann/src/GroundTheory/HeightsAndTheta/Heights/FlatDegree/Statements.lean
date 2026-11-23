import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.FlatTheorem

open Matrix NumberField

section Period

variable {n : ℕ}

def hermForm (H : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ :=
  star x ⬝ᵥ (H *ᵥ y)

def gram (H : Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (u : Fin m → Fin n → ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j ↦ hermForm H (u i) (u j)

structure PeriodPoint (p q : ℕ) (H : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) where

  plus : Submodule ℂ (Fin (p + q) → ℂ)

  minus : Submodule ℂ (Fin (p + q) → ℂ)
  isCompl : IsCompl plus minus
  orth : ∀ x ∈ plus, ∀ y ∈ minus, hermForm H x y = 0
  finrank_plus : Module.finrank ℂ plus = p
  finrank_minus : Module.finrank ℂ minus = q
  pos : ∀ x ∈ plus, x ≠ 0 → 0 < (hermForm H x x).re
  neg : ∀ x ∈ minus, x ≠ 0 → (hermForm H x x).re < 0

variable {p q : ℕ} {H : Matrix (Fin (p + q)) (Fin (p + q)) ℂ}

def PeriodPoint.proj (y : PeriodPoint p q H) (x : Fin (p + q) → ℂ) : Fin (p + q) → ℂ :=
  (Submodule.projectionOnto y.plus y.minus y.isCompl x : Fin (p + q) → ℂ)

def hodgeNormSq (y : PeriodPoint p q H) (v : Fin p → Fin (p + q) → ℂ)
    (f : Fin q → Fin (p + q) → ℂ) : ℝ :=
  (gram H (fun i ↦ y.proj (v i))).det.re * (gram (-H) f).det.re

def frameMatrix (v : Fin p → Fin (p + q) → ℂ) (f : Fin q → Fin (p + q) → ℂ) :
    Matrix (Fin (p + q)) (Fin (p + q)) ℂ :=
  Matrix.of fun i k ↦ Fin.append v f k i

end Period

def FlatNormConstant.Statement : Prop :=
  ∀ (p q : ℕ) (H : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), H.IsHermitian →
    ∀ (y : PeriodPoint p q H) (v : Fin p → Fin (p + q) → ℂ) (f : Fin q → Fin (p + q) → ℂ),
      (∀ k, f k ∈ y.minus) →
        hodgeNormSq y v f = Complex.normSq (frameMatrix v f).det * |H.det.re|

def DifferentNorms.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E],
    (Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) : ℝ) ^ ((Module.finrank ℚ E : ℝ)⁻¹) =
        rootDiscr E / rootDiscr K ∧
      (Ideal.absNorm ((differentIdeal ℤ (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 E))) : ℝ) ^
          ((Module.finrank ℚ E : ℝ)⁻¹) = rootDiscr K ∧
      1 ≤ rootDiscr K ∧ rootDiscr K ≤ rootDiscr E

def FlatDegreeBound.Statement : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (p q : ℕ) (logΩ c : ℝ),
    c = -(((p : ℝ) - q) / 2 * logΩ +
        q * (2 * Real.log (rootDiscr K) - Real.log (rootDiscr E))) →
      |c + ((p : ℝ) - q) / 2 * logΩ| ≤ q * Real.log (rootDiscr E)

section Examples

theorem hermForm_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a b : ℂ) (x y : Fin n → ℂ) :
    hermForm H (a • x) (b • y) = star a * b * hermForm H x y := by
  simp only [hermForm, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct,
    smul_eq_mul]
  ring

def exH : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ := Matrix.diagonal ![1, -1]

theorem exH_isHermitian : exH.IsHermitian := by
  rw [exH, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  fin_cases i <;> simp

def exU : Fin (1 + 1) → ℂ := ![1, 1 / 2]

def exW : Fin (1 + 1) → ℂ := ![1 / 2, 1]

theorem exU_exW : hermForm exH exU exW = 0 := by
  simp [hermForm, exH, exU, exW, dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.diagonal, map_ofNat]
  try norm_num

theorem exU_exU : hermForm exH exU exU = 3 / 4 := by
  simp [hermForm, exH, exU, dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.diagonal, map_ofNat]
  try norm_num

theorem exW_exW : hermForm exH exW exW = -3 / 4 := by
  simp [hermForm, exH, exW, dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.diagonal, map_ofNat]
  try norm_num

theorem exU_ne : exU ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [exU] at this

theorem exW_ne : exW ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [exW] at this

theorem ex_isCompl : IsCompl (ℂ ∙ exU) (ℂ ∙ exW) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
    have h0 := congrFun hb 0
    have h1 := congrFun hb 1
    simp [exU, exW] at h0 h1
    have ha : a = 0 := by linear_combination (-4 / 3 : ℂ) * h0 + (2 / 3 : ℂ) * h1
    simp [ha]
  · rw [codisjoint_iff, eq_top_iff]
    intro z _
    rw [Submodule.mem_sup]
    refine ⟨((4 * z 0 - 2 * z 1) / 3) • exU, Submodule.mem_span_singleton.mpr ⟨_, rfl⟩,
      ((4 * z 1 - 2 * z 0) / 3) • exW, Submodule.mem_span_singleton.mpr ⟨_, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [exU, exW] <;> ring

def exPoint : PeriodPoint 1 1 exH where
  plus := ℂ ∙ exU
  minus := ℂ ∙ exW
  isCompl := ex_isCompl
  orth := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [hermForm_smul, exU_exW, mul_zero]
  finrank_plus := finrank_span_singleton exU_ne
  finrank_minus := finrank_span_singleton exW_ne
  pos := by
    intro x hx hx0
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have ha : a ≠ 0 := by rintro rfl; simp at hx0
    rw [hermForm_smul, exU_exU]
    have : star a * a = ((Complex.normSq a : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [this]
    have hpos : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    norm_num
    exact ha
  neg := by
    intro x hx hx0
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have ha : a ≠ 0 := by rintro rfl; simp at hx0
    rw [hermForm_smul, exW_exW]
    have : star a * a = ((Complex.normSq a : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [this]
    have hpos : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    norm_num
    exact ha

theorem FlatNormConstant.hypotheses_example :
    exH.IsHermitian ∧ ∀ k, (![exW] : Fin 1 → Fin (1 + 1) → ℂ) k ∈ exPoint.minus := by
  refine ⟨exH_isHermitian, fun k ↦ ?_⟩
  fin_cases k
  exact Submodule.mem_span_singleton_self exW

theorem FlatNormConstant.at_example (h : FlatNormConstant.Statement) :
    hodgeNormSq exPoint ![![1, 0]] ![exW] =
      Complex.normSq (frameMatrix ![![1, 0]] ![exW]).det * |exH.det.re| :=
  h 1 1 exH exH_isHermitian exPoint _ _ FlatNormConstant.hypotheses_example.2

theorem DifferentNorms.at_example (h : DifferentNorms.Statement) :
    (Ideal.absNorm (differentIdeal (𝓞 ℚ) (𝓞 (CyclotomicField 4 ℚ))) : ℝ) ^
        ((Module.finrank ℚ (CyclotomicField 4 ℚ) : ℝ)⁻¹) =
      rootDiscr (CyclotomicField 4 ℚ) / rootDiscr ℚ :=
  (h ℚ (CyclotomicField 4 ℚ)).1

theorem FlatDegreeBound.hypotheses_example :
    let c : ℝ := -((((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) / 2 * 1 +
        ((1 : ℕ) : ℝ) * (2 * Real.log (rootDiscr ℚ) -
          Real.log (rootDiscr (CyclotomicField 4 ℚ))))
    c = -((((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) / 2 * 1 +
        ((1 : ℕ) : ℝ) * (2 * Real.log (rootDiscr ℚ) -
          Real.log (rootDiscr (CyclotomicField 4 ℚ)))) := rfl

theorem FlatDegreeBound.at_example (h : FlatDegreeBound.Statement) :
    |-((((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) / 2 * 1 +
        ((1 : ℕ) : ℝ) * (2 * Real.log (rootDiscr ℚ) -
          Real.log (rootDiscr (CyclotomicField 4 ℚ)))) +
        (((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) / 2 * 1| ≤
      ((1 : ℕ) : ℝ) * Real.log (rootDiscr (CyclotomicField 4 ℚ)) :=
  h ℚ (CyclotomicField 4 ℚ) 2 1 1 _ FlatDegreeBound.hypotheses_example

end Examples

end GroundTheory.Heights₂.Heights.FlatTheorem
