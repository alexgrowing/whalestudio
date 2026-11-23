import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.VariableChangePoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open WeierstrassCurve OnePoint

variable {F : Type*} [Field F]

structure IsShortForm (W : WeierstrassCurve F) : Prop where
  a₁_eq : W.a₁ = 0
  a₂_eq : W.a₂ = 0
  a₃_eq : W.a₃ = 0

namespace ShortWeierstrass

def g₂ (W : WeierstrassCurve F) : F := -4 * W.a₄

def g₃ (W : WeierstrassCurve F) : F := -4 * W.a₆

end ShortWeierstrass

open ShortWeierstrass

theorem IsShortForm.Δ_eq {W : WeierstrassCurve F} (hW : IsShortForm W) :
    W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq]
  ring

theorem IsShortForm.Δ_eq_g {W : WeierstrassCurve F} (hW : IsShortForm W) :
    W.Δ = g₂ W ^ 3 - 27 * g₃ W ^ 2 := by
  rw [hW.Δ_eq, g₂, g₃]
  ring

theorem IsShortForm.a₄_ne_zero_or_a₆_ne_zero {W : WeierstrassCurve F} [W.IsElliptic]
    (hW : IsShortForm W) : W.a₄ ≠ 0 ∨ W.a₆ ≠ 0 := by
  by_contra h
  push Not at h
  have := W.isUnit_Δ.ne_zero
  rw [hW.Δ_eq, h.1, h.2] at this
  simp at this

open scoped Classical in

noncomputable def weberValue (W : WeierstrassCurve F) (x : F) : F :=
  if W.a₆ = 0 then g₂ W ^ 2 / W.Δ * x ^ 2
  else if W.a₄ = 0 then g₃ W / W.Δ * x ^ 3
  else g₂ W * g₃ W / W.Δ * x

noncomputable def weberFunction (W : WeierstrassCurve F) : W.toAffine.Point → OnePoint F
  | .zero => ∞
  | .some x _ _ => OnePoint.some (weberValue W x)

@[simp]
theorem weberFunction_zero (W : WeierstrassCurve F) : weberFunction W .zero = ∞ := rfl

@[simp]
theorem weberFunction_some (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
    weberFunction W (.some x y h) = OnePoint.some (weberValue W x) := rfl

theorem weberValue_of_a₆_eq_zero {W : WeierstrassCurve F} (hb : W.a₆ = 0) (x : F) :
    weberValue W x = g₂ W ^ 2 / W.Δ * x ^ 2 := by
  simp [weberValue, hb]

theorem weberValue_of_a₄_eq_zero {W : WeierstrassCurve F} (ha : W.a₄ = 0) (hb : W.a₆ ≠ 0)
    (x : F) : weberValue W x = g₃ W / W.Δ * x ^ 3 := by
  simp [weberValue, ha, hb]

theorem weberValue_of_ne_zero {W : WeierstrassCurve F} (ha : W.a₄ ≠ 0) (hb : W.a₆ ≠ 0)
    (x : F) : weberValue W x = g₂ W * g₃ W / W.Δ * x := by
  simp [weberValue, ha, hb]

section Isomorphism

variable [CharZero F]

theorem variableChange_rst_eq_zero {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  have h1 := hCW.a₁_eq
  have h2 := hCW.a₂_eq
  have h3 := hCW.a₃_eq
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, hW.a₁_eq, hW.a₂_eq,
    hW.a₃_eq] at h1 h2 h3
  have hs : C.s = 0 := by simpa [hv] using h1
  have ht : C.t = 0 := by simpa [hv] using h3
  have hr : C.r = 0 := by simpa [hv, hs] using h2
  exact ⟨hr, hs, ht⟩

theorem variableChange_a₄_of_isShortForm {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₄ = ↑C.u⁻¹ ^ 4 * W.a₄ := by
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hCW
  simp [variableChange_a₄, hr, hs, ht]

theorem variableChange_a₆_of_isShortForm {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₆ = ↑C.u⁻¹ ^ 6 * W.a₆ := by
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hCW
  simp [variableChange_a₆, hr, ht]

theorem weberFunction_variableChangePoint (C : VariableChange F) {W W' : WeierstrassCurve F}
    [W.IsElliptic] (hC : C • W = W') (hW : IsShortForm W) (hW' : IsShortForm W')
    (P : W.toAffine.Point) :
    weberFunction W' (variableChangePoint C hC P) = weberFunction W P := by
  subst hC
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hW'
  cases P with
  | zero => rfl
  | some x y h =>
    rw [variableChangePoint_some, weberFunction_some, weberFunction_some]
    congr 1
    have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
    have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
    have ha := variableChange_a₄_of_isShortForm hW hW'
    have hb := variableChange_a₆_of_isShortForm hW hW'
    have hb0 : (C • W).a₆ = 0 ↔ W.a₆ = 0 := by rw [hb]; simp
    have ha0 : (C • W).a₄ = 0 ↔ W.a₄ = 0 := by rw [ha]; simp
    by_cases h6 : W.a₆ = 0
    · rw [weberValue_of_a₆_eq_zero (hb0.mpr h6), weberValue_of_a₆_eq_zero h6]
      simp only [g₂, ha, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp
    by_cases h4 : W.a₄ = 0
    · rw [weberValue_of_a₄_eq_zero (ha0.mpr h4) (mt hb0.mp h6), weberValue_of_a₄_eq_zero h4 h6]
      simp only [g₃, hb, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp
    · rw [weberValue_of_ne_zero (mt ha0.mp h4) (mt hb0.mp h6), weberValue_of_ne_zero h4 h6]
      simp only [g₂, g₃, ha, hb, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp

end Isomorphism

section FieldOfDefinition

variable {L : Type*} [Field L]

def pointMapOfRingHom (φ : F →+* L) {W : WeierstrassCurve F} :
    W.toAffine.Point → (W.map φ).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (φ x) (φ y) ((W.toAffine.map_nonsingular φ.injective x y).mpr h)

theorem weberFunction_pointMapOfRingHom (φ : F →+* L) (W : WeierstrassCurve F)
    (P : W.toAffine.Point) :
    weberFunction (W.map φ) (pointMapOfRingHom φ P) = OnePoint.map φ (weberFunction W P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    have h4 : (W.map φ).a₄ = φ W.a₄ := rfl
    have h6 : (W.map φ).a₆ = φ W.a₆ := rfl
    show OnePoint.some _ = OnePoint.some _
    congr 1
    by_cases hb : W.a₆ = 0
    · rw [weberValue_of_a₆_eq_zero (by rw [h6, hb, map_zero]), weberValue_of_a₆_eq_zero hb]
      simp [g₂, map_Δ, map_ofNat]
    have hb' : (W.map φ).a₆ ≠ 0 := by rw [h6]; exact (map_ne_zero φ).mpr hb
    by_cases ha : W.a₄ = 0
    · rw [weberValue_of_a₄_eq_zero (by rw [h4, ha, map_zero]) hb', weberValue_of_a₄_eq_zero ha hb]
      simp [g₃, map_Δ, map_ofNat]
    · have ha' : (W.map φ).a₄ ≠ 0 := by rw [h4]; exact (map_ne_zero φ).mpr ha
      rw [weberValue_of_ne_zero ha' hb', weberValue_of_ne_zero ha hb]
      simp [g₂, g₃, map_Δ, map_ofNat]

end FieldOfDefinition

end GroundTheory.Global
