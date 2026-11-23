import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyPoints
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KernelCard
import GroundTheory.ArithmeticGeometry.SchemeCohomology.KaehlerPlace

namespace GroundTheory.Global

open Polynomial KaehlerDifferential GroundTheory.Arith.Abelian IntermediateField
open WeierstrassCurve.Affine (Point equation_iff nonsingular_iff')

universe u v

section Identities

variable {R : Type*} [CommRing R]

private theorem chord_identities {a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ x₃ y₃ l : R}
    (hl : l * (x₁ - x₂) = y₁ - y₂)
    (e₁ : y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆)
    (e₂ : y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆)
    (hx : x₃ = l ^ 2 + a₁ * l - a₂ - x₁ - x₂)
    (hy : y₃ = -(l * (x₃ - x₁) + y₁) - a₁ * x₃ - a₃) :
    ((2 * l + a₁) * ((3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) - l * (2 * y₁ + a₁ * x₁ + a₃)) -
        (x₁ - x₂) * (2 * y₁ + a₁ * x₁ + a₃)) * (x₁ - x₂) =
      (x₁ - x₂) * (x₁ - x₂) * (2 * y₃ + a₁ * x₃ + a₃) ∧
    (-(2 * l + a₁) * ((3 * x₂ ^ 2 + 2 * a₂ * x₂ + a₄ - a₁ * y₂) - l * (2 * y₂ + a₁ * x₂ + a₃)) -
        (x₁ - x₂) * (2 * y₂ + a₁ * x₂ + a₃)) * (x₁ - x₂) =
      (x₁ - x₂) * (x₁ - x₂) * (2 * y₃ + a₁ * x₃ + a₃) ∧
    (-(x₃ - x₁) * ((3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) - l * (2 * y₁ + a₁ * x₁ + a₃)) -
        (l + a₁) * (x₁ - x₂) * (2 * y₃ + a₁ * x₃ + a₃) + l * (x₁ - x₂) * (2 * y₁ + a₁ * x₁ + a₃) -
        (x₁ - x₂) * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁)) * (x₁ - x₂) =
      (x₁ - x₂) * (x₁ - x₂) * (3 * x₃ ^ 2 + 2 * a₂ * x₃ + a₄ - a₁ * y₃) ∧
    ((x₃ - x₁) * ((3 * x₂ ^ 2 + 2 * a₂ * x₂ + a₄ - a₁ * y₂) - l * (2 * y₂ + a₁ * x₂ + a₃)) -
        (l + a₁) * (x₁ - x₂) * (2 * y₃ + a₁ * x₃ + a₃)) * (x₁ - x₂) =
      (x₁ - x₂) * (x₁ - x₂) * (3 * x₃ ^ 2 + 2 * a₂ * x₃ + a₄ - a₁ * y₃) := by
  subst hy
  subst hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-a₁^2*x₂ - a₁*a₃ + a₁*l*x₁ - 3*a₁*l*x₂ - a₁*y₁ - a₁*y₂ - 2*a₃*l + 2*l^2*x₁ -
      2*l^2*x₂ - 2*l*y₁ - 2*l*y₂) * hl + (-a₁ - 2*l) * e₁ + (a₁ + 2*l) * e₂
  · linear_combination (a₁^2*x₁ + a₁*a₃ + 3*a₁*l*x₁ - a₁*l*x₂ + a₁*y₁ + a₁*y₂ + 2*a₃*l + 2*l^2*x₁ -
      2*l^2*x₂ + 2*l*y₁ + 2*l*y₂ - 2*x₁^2 + 4*x₁*x₂ - 2*x₂^2) * hl + (a₁ + 2*l) * e₁ +
      (-a₁ - 2*l) * e₂
  · linear_combination (a₁^2*l*x₂ - a₁*a₂*x₂ + a₁*a₃*l - a₁*l^2*x₁ + 2*a₁*l^2*x₂ + a₁*l*y₁ +
      a₁*l*y₂ - 3*a₁*x₂^2 - a₂*a₃ + a₂*l*x₁ - a₂*l*x₂ - a₂*y₁ - a₂*y₂ + a₃*l^2 - 3*a₃*x₂ - l^3*x₁ +
      l^3*x₂ + l^2*y₁ + l^2*y₂ + 3*l*x₁*x₂ - 3*l*x₂^2 - 3*x₂*y₁ - 3*x₂*y₂) * hl +
      (a₁*l - a₂ + l^2 - 3*x₂) * e₁ + (-a₁*l + a₂ - l^2 + 3*x₂) * e₂
  · linear_combination (-a₁^2*l*x₁ + a₁*a₂*x₁ - a₁*a₃*l - 2*a₁*l^2*x₁ + a₁*l^2*x₂ - a₁*l*y₁ -
      a₁*l*y₂ + 2*a₁*x₁^2 + 2*a₁*x₁*x₂ - a₁*x₂^2 + a₂*a₃ + a₂*l*x₁ - a₂*l*x₂ + a₂*y₁ + a₂*y₂ -
      a₃*l^2 + 3*a₃*x₁ - l^3*x₁ + l^3*x₂ - l^2*y₁ - l^2*y₂ + l*x₁^2 + l*x₁*x₂ - 2*l*x₂^2 +
      3*x₁*y₁ + 3*x₁*y₂) * hl + (-a₁*l + a₂ - l^2 + 3*x₁) * e₁ + (a₁*l - a₂ + l^2 - 3*x₁) * e₂

private theorem tangent_identities {a₁ a₂ a₃ a₄ x₁ y₁ x₃ y₃ l : R}
    (hl : l * (2 * y₁ + a₁ * x₁ + a₃) = 3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁)
    (hx : x₃ = l ^ 2 + a₁ * l - a₂ - x₁ - x₁)
    (hy : y₃ = -(l * (x₃ - x₁) + y₁) - a₁ * x₃ - a₃) :
    (2 * l + a₁) * ((6 * x₁ + 2 * a₂) * (2 * y₁ + a₁ * x₁ + a₃) -
        a₁ * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) -
        l * (2 * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) + a₁ * (2 * y₁ + a₁ * x₁ + a₃))) -
        2 * (2 * y₁ + a₁ * x₁ + a₃) * (2 * y₁ + a₁ * x₁ + a₃) =
      2 * (2 * y₁ + a₁ * x₁ + a₃) * (2 * y₃ + a₁ * x₃ + a₃) ∧
    -(x₃ - x₁) * ((6 * x₁ + 2 * a₂) * (2 * y₁ + a₁ * x₁ + a₃) -
        a₁ * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) -
        l * (2 * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) + a₁ * (2 * y₁ + a₁ * x₁ + a₃))) -
        (l + a₁) * (2 * (2 * y₁ + a₁ * x₁ + a₃) * (2 * y₃ + a₁ * x₃ + a₃)) +
        l * (2 * y₁ + a₁ * x₁ + a₃) * (2 * y₁ + a₁ * x₁ + a₃) -
        (2 * y₁ + a₁ * x₁ + a₃) * (3 * x₁ ^ 2 + 2 * a₂ * x₁ + a₄ - a₁ * y₁) =
      2 * (2 * y₁ + a₁ * x₁ + a₃) * (3 * x₃ ^ 2 + 2 * a₂ * x₃ + a₄ - a₁ * y₃) := by
  subst hy
  subst hx
  refine ⟨?_, ?_⟩
  · linear_combination (a₁^2 + 4*a₁*l + 4*l^2) * hl
  · linear_combination (-a₁^2*l + a₁*a₂ - 3*a₁*l^2 + 6*a₁*x₁ + 2*a₂*l + 3*a₃ - 2*l^3 + 6*l*x₁ +
      6*y₁) * hl

end Identities

section AtPoint

variable {F : Type u} [Field F] (E : WeierstrassCurve F) {L : Type v} [Field L] [Algebra F L]

open Classical in

noncomputable def omegaAt : (E.baseChange L).toAffine.Point → Ω[L⁄F]
  | .zero => 0
  | .some x y _ =>
    if 2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃ ≠ 0 then
      (2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃)⁻¹ • D F L x
    else
      (3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
        (E.baseChange L).a₁ * y)⁻¹ • D F L y

@[simp]
theorem omegaAt_zero : omegaAt E (0 : (E.baseChange L).toAffine.Point) = 0 := rfl

theorem D_coeff (c : F) : D F L (algebraMap F L c) = 0 := (D F L).map_algebraMap c

theorem D_equation {x y : L} (h : (E.baseChange L).toAffine.Equation x y) :
    (2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃) • D F L y =
      (3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
        (E.baseChange L).a₁ * y) • D F L x := by
  have e := congrArg (D F L) ((equation_iff _ _).mp h)
  have h1 : D F L (E.baseChange L).a₁ = 0 := D_coeff E.a₁
  have h2 : D F L (E.baseChange L).a₂ = 0 := D_coeff E.a₂
  have h3 : D F L (E.baseChange L).a₃ = 0 := D_coeff E.a₃
  have h4 : D F L (E.baseChange L).a₄ = 0 := D_coeff E.a₄
  have h6 : D F L (E.baseChange L).a₆ = 0 := D_coeff E.a₆
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, h1, h2, h3, h4, h6, smul_zero,
    add_zero] at e
  linear_combination (norm := module) e

theorem omegaAt_some_spec {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) :
    (2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃) • omegaAt E (.some x y h) =
        D F L x ∧
      (3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
        (E.baseChange L).a₁ * y) • omegaAt E (.some x y h) = D F L y := by
  have rel := D_equation E h.1
  have hns := ((nonsingular_iff' _ _).mp h).2
  set a := 2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃ with ha
  set b := 3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
    (E.baseChange L).a₁ * y with hb
  have hb' : (E.baseChange L).a₁ * y - (3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x +
      (E.baseChange L).a₄) = -b := by rw [hb]; ring
  rw [hb', neg_ne_zero] at hns
  by_cases hu : a ≠ 0
  · have e : omegaAt E (.some x y h) = a⁻¹ • D F L x := by
      simp only [omegaAt, ← ha, if_pos hu]
    rw [e, smul_smul, mul_inv_cancel₀ hu, one_smul, smul_smul, mul_comm, ← smul_smul, ← rel,
      smul_smul, inv_mul_cancel₀ hu, one_smul]
    exact ⟨rfl, rfl⟩
  · have e : omegaAt E (.some x y h) = b⁻¹ • D F L y := by
      simp only [omegaAt, ← ha, ← hb, if_neg hu]
    rw [not_not] at hu
    have hb0 : b ≠ 0 := hns.resolve_right (fun h' => h' hu)
    have hx : D F L x = 0 := by
      have := rel
      rw [hu, zero_smul] at this
      exact (smul_eq_zero.mp this.symm).resolve_left hb0
    rw [e, hu, zero_smul, hx, smul_smul, mul_inv_cancel₀ hb0, one_smul]
    exact ⟨rfl, rfl⟩

theorem omegaAt_some_eq {x y : L} (h : (E.baseChange L).toAffine.Nonsingular x y) {η : Ω[L⁄F]}
    (h₁ : (2 * y + (E.baseChange L).a₁ * x + (E.baseChange L).a₃) • η = D F L x)
    (h₂ : (3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
        (E.baseChange L).a₁ * y) • η = D F L y) :
    omegaAt E (.some x y h) = η := by
  obtain ⟨s₁, s₂⟩ := omegaAt_some_spec E h
  have hns := ((nonsingular_iff' _ _).mp h).2
  rcases hns with hp | hu
  · have hp' : 3 * x ^ 2 + 2 * (E.baseChange L).a₂ * x + (E.baseChange L).a₄ -
        (E.baseChange L).a₁ * y ≠ 0 := by
      intro h0; apply hp; linear_combination -h0
    exact smul_right_injective _ hp' (s₂.trans h₂.symm)
  · exact smul_right_injective _ hu (s₁.trans h₁.symm)

end AtPoint

section Add

variable {F : Type u} [Field F] (E : WeierstrassCurve F) {L : Type v} [Field L] [Algebra F L]

theorem D_two : D F L (2 : L) = 0 := by simpa using (D F L).map_natCast 2

theorem D_three : D F L (3 : L) = 0 := by simpa using (D F L).map_natCast 3

theorem D_addX (x₁ x₂ l : L) :
    D F L ((E.baseChange L).toAffine.addX x₁ x₂ l) =
      (2 * l + (E.baseChange L).a₁) • D F L l - D F L x₁ - D F L x₂ := by
  have h1 : D F L (E.baseChange L).a₁ = 0 := D_coeff E.a₁
  have h2 : D F L (E.baseChange L).a₂ = 0 := D_coeff E.a₂
  simp only [WeierstrassCurve.Affine.addX, map_sub, map_add, Derivation.leibniz,
    Derivation.leibniz_pow, h1, h2, smul_zero, add_zero]
  module

theorem D_addY (x₁ x₂ y₁ l : L) :
    D F L ((E.baseChange L).toAffine.addY x₁ x₂ y₁ l) =
      -(l • (D F L ((E.baseChange L).toAffine.addX x₁ x₂ l) - D F L x₁) +
        ((E.baseChange L).toAffine.addX x₁ x₂ l - x₁) • D F L l) - D F L y₁ -
        (E.baseChange L).a₁ • D F L ((E.baseChange L).toAffine.addX x₁ x₂ l) := by
  have h1 : D F L (E.baseChange L).a₁ = 0 := D_coeff E.a₁
  have h3 : D F L (E.baseChange L).a₃ = 0 := D_coeff E.a₃
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, map_sub, map_add, map_neg, Derivation.leibniz, h1, h3,
    smul_zero, add_zero, sub_zero]
  module

variable [DecidableEq L]

theorem omegaAt_neg (P : (E.baseChange L).toAffine.Point) : omegaAt E (-P) = -omegaAt E P := by
  rcases P with _ | ⟨x, y, h⟩
  · show omegaAt E (-0) = -omegaAt E 0
    simp
  · obtain ⟨s, t⟩ := omegaAt_some_spec E h
    have h1 : D F L (E.baseChange L).a₁ = 0 := D_coeff E.a₁
    have h3 : D F L (E.baseChange L).a₃ = 0 := D_coeff E.a₃
    rw [Point.neg_some]
    refine omegaAt_some_eq E _ ?_ ?_
    · rw [← s]
      simp only [WeierstrassCurve.Affine.negY]
      module
    · simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, Derivation.leibniz, h1, h3,
        smul_zero, add_zero, sub_zero, ← s, ← t]
      module

theorem omegaAt_add (P Q : (E.baseChange L).toAffine.Point) :
    omegaAt E (P + Q) = omegaAt E P + omegaAt E Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · show omegaAt E (0 + 0) = omegaAt E 0 + omegaAt E 0
    simp
  · show omegaAt E (0 + _) = omegaAt E 0 + _
    simp
  · show omegaAt E (_ + 0) = _ + omegaAt E 0
    simp
  by_cases hxy : x₁ = x₂ ∧ y₁ = (E.baseChange L).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, omegaAt_zero]
    obtain ⟨rfl, rfl⟩ := hxy
    have e : (Point.some x₁ ((E.baseChange L).toAffine.negY x₁ y₂) h₁ :
        (E.baseChange L).toAffine.Point) = -Point.some x₁ y₂ h₂ := rfl
    rw [e, omegaAt_neg, neg_add_cancel]
  rw [Point.add_some hxy]
  obtain ⟨s₁, t₁⟩ := omegaAt_some_spec E h₁
  obtain ⟨s₂, t₂⟩ := omegaAt_some_spec E h₂
  have e₁ := (equation_iff _ _).mp h₁.1
  have e₂ := (equation_iff _ _).mp h₂.1
  have ha₁ : D F L (E.baseChange L).a₁ = 0 := D_coeff E.a₁
  have ha₂ : D F L (E.baseChange L).a₂ = 0 := D_coeff E.a₂
  have ha₃ : D F L (E.baseChange L).a₃ = 0 := D_coeff E.a₃
  have ha₄ : D F L (E.baseChange L).a₄ = 0 := D_coeff E.a₄
  set l := (E.baseChange L).toAffine.slope x₁ x₂ y₁ y₂ with hl_def
  set ω₁ := omegaAt E (Point.some x₁ y₁ h₁)
  set ω₂ := omegaAt E (Point.some x₂ y₂ h₂)
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (E.baseChange L).toAffine.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    obtain rfl := hx
    obtain rfl := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁.1 h₂.1 rfl hy
    have hω : ω₂ = ω₁ := rfl
    have hu : y₁ - (E.baseChange L).toAffine.negY x₁ y₁ =
        2 * y₁ + (E.baseChange L).a₁ * x₁ + (E.baseChange L).a₃ := by
      simp only [WeierstrassCurve.Affine.negY]; ring
    have hu0 : 2 * y₁ + (E.baseChange L).a₁ * x₁ + (E.baseChange L).a₃ ≠ 0 := by
      rw [← hu]; exact sub_ne_zero.mpr hy
    have hl : l * (2 * y₁ + (E.baseChange L).a₁ * x₁ + (E.baseChange L).a₃) =
        3 * x₁ ^ 2 + 2 * (E.baseChange L).a₂ * x₁ + (E.baseChange L).a₄ -
          (E.baseChange L).a₁ * y₁ := by
      rw [hl_def, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hu, div_mul_cancel₀ _ hu0]
    have hDl := congrArg (D F L) hl
    simp only [Derivation.leibniz, map_add, map_sub, Derivation.leibniz_pow, ha₁, ha₂, ha₃, ha₄,
      D_two, D_three, smul_zero, add_zero] at hDl
    rw [← s₁, ← t₁] at hDl
    obtain ⟨iE, iF⟩ := tangent_identities (x₃ := (E.baseChange L).toAffine.addX x₁ x₁ l)
      (y₃ := (E.baseChange L).toAffine.addY x₁ x₁ y₁ l) hl rfl rfl
    have hX : (2 * (E.baseChange L).toAffine.addY x₁ x₁ y₁ l +
        (E.baseChange L).a₁ * (E.baseChange L).toAffine.addX x₁ x₁ l + (E.baseChange L).a₃) •
          (ω₁ + ω₂) = D F L ((E.baseChange L).toAffine.addX x₁ x₁ l) := by
      rw [hω]
      refine smul_right_injective _ hu0 ?_
      beta_reduce
      rw [D_addX, ← s₁]
      linear_combination (norm := module) (-(2 * l + (E.baseChange L).a₁)) • hDl - iE • ω₁
    refine omegaAt_some_eq E _ hX ?_
    refine smul_right_injective _ hu0 ?_
    beta_reduce
    rw [D_addY, ← hX, hω, ← s₁, ← t₁]
    linear_combination (norm := module)
      ((E.baseChange L).toAffine.addX x₁ x₁ l - x₁) • hDl - iF • ω₁
  · have hs : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have hl : l * (x₁ - x₂) = y₁ - y₂ := by
      rw [hl_def, WeierstrassCurve.Affine.slope_of_X_ne hx, div_mul_cancel₀ _ hs]
    have hDl := congrArg (D F L) hl
    simp only [Derivation.leibniz, map_sub] at hDl
    rw [← s₁, ← s₂, ← t₁, ← t₂] at hDl
    obtain ⟨iA, iB, iC, iD⟩ := chord_identities (x₃ := (E.baseChange L).toAffine.addX x₁ x₂ l)
      (y₃ := (E.baseChange L).toAffine.addY x₁ x₂ y₁ l) hl e₁ e₂ rfl rfl
    have hX : (2 * (E.baseChange L).toAffine.addY x₁ x₂ y₁ l +
        (E.baseChange L).a₁ * (E.baseChange L).toAffine.addX x₁ x₂ l + (E.baseChange L).a₃) •
          (ω₁ + ω₂) = D F L ((E.baseChange L).toAffine.addX x₁ x₂ l) := by
      refine smul_right_injective _ (mul_ne_zero hs hs) ?_
      beta_reduce
      rw [D_addX, ← s₁, ← s₂]
      linear_combination (norm := module)
        (-((x₁ - x₂) * (2 * l + (E.baseChange L).a₁))) • hDl - iA • ω₁ - iB • ω₂
    refine omegaAt_some_eq E _ hX ?_
    refine smul_right_injective _ (mul_ne_zero hs hs) ?_
    beta_reduce
    rw [D_addY, ← hX, ← s₁, ← t₁]
    linear_combination (norm := module)
      ((x₁ - x₂) * ((E.baseChange L).toAffine.addX x₁ x₂ l - x₁)) • hDl - iC • ω₁ - iD • ω₂

noncomputable def omegaHom : (E.baseChange L).toAffine.Point →+ Ω[L⁄F] :=
  AddMonoidHom.mk' (omegaAt E) (omegaAt_add E)

theorem omegaAt_zsmul (n : ℤ) (P : (E.baseChange L).toAffine.Point) :
    omegaAt E (n • P) = n • omegaAt E P :=
  map_zsmul (omegaHom E) n P

end Add

section Push

variable {F : Type u} [Field F] {L L' : Type*} [Field L] [Algebra F L] [Field L'] [Algebra F L']

noncomputable def kpush (σ : L →ₐ[F] L') : Ω[L⁄F] →+ Ω[L'⁄F] :=
  letI : Algebra L L' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower F L L' := IsScalarTower.of_algebraMap_eq fun a => (σ.commutes a).symm
  (KaehlerDifferential.map F F L L').toAddMonoidHom

theorem kpush_D (σ : L →ₐ[F] L') (a : L) : kpush σ (D F L a) = D F L' (σ a) := by
  let _ : Algebra L L' := σ.toRingHom.toAlgebra
  have _ : IsScalarTower F L L' := IsScalarTower.of_algebraMap_eq fun a => (σ.commutes a).symm
  exact KaehlerDifferential.map_D F F L L' a

theorem kpush_smul (σ : L →ₐ[F] L') (a : L) (η : Ω[L⁄F]) :
    kpush σ (a • η) = σ a • kpush σ η := by
  let _ : Algebra L L' := σ.toRingHom.toAlgebra
  have _ : IsScalarTower F L L' := IsScalarTower.of_algebraMap_eq fun a => (σ.commutes a).symm
  show KaehlerDifferential.map F F L L' (a • η) = _
  rw [LinearMap.map_smul]
  exact (algebraMap_smul L' a _).symm

variable (E : WeierstrassCurve F) [DecidableEq L] [DecidableEq L']

theorem kpush_omegaAt (σ : L →ₐ[F] L') (P : (E.baseChange L).toAffine.Point) :
    kpush σ (omegaAt E P) = omegaAt E (Point.map σ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · show kpush σ (omegaAt E 0) = omegaAt E (Point.map σ 0)
    rw [map_zero, omegaAt_zero, omegaAt_zero, map_zero]
  · rw [Point.map_some]
    obtain ⟨s, t⟩ := omegaAt_some_spec E h
    have c1 : (E.baseChange L').a₁ = σ (E.baseChange L).a₁ := (σ.commutes E.a₁).symm
    have c2 : (E.baseChange L').a₂ = σ (E.baseChange L).a₂ := (σ.commutes E.a₂).symm
    have c3 : (E.baseChange L').a₃ = σ (E.baseChange L).a₃ := (σ.commutes E.a₃).symm
    have c4 : (E.baseChange L').a₄ = σ (E.baseChange L).a₄ := (σ.commutes E.a₄).symm
    refine (omegaAt_some_eq E _ ?_ ?_).symm
    · rw [c1, c3, ← kpush_D, ← s, kpush_smul]
      simp only [map_add, map_mul, map_ofNat]
    · rw [c1, c2, c4, ← kpush_D, ← t, kpush_smul]
      simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]

end Push

section Invariant

variable {F : Type u} [Field F] (E : WeierstrassCurve F)

instance isFunctionField_functionField :
    GroundTheory.FunctionField.IsFunctionField F E.toAffine.FunctionField :=
  ⟨⟨genX E, transcendental_genX E, Module.finite_of_finrank_pos (by
    rw [finrank_adjoin_genX E]; norm_num)⟩⟩

variable [E.IsElliptic]

theorem genDen_ne_zero :
    2 * genY E + algebraMap F E.toAffine.FunctionField E.a₁ * genX E +
      algebraMap F E.toAffine.FunctionField E.a₃ ≠ 0 := by
  intro h0
  apply Ψ₂Sq_ne_zero E
  rw [← aeval_genX_eq_zero_iff]
  have e := (equation_iff _ _).mp (equation_gen E)
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, map_add, map_mul, map_pow, aeval_C, aeval_X, map_ofNat]
  linear_combination (2 * genY E + algebraMap F E.toAffine.FunctionField E.a₁ * genX E +
      algebraMap F E.toAffine.FunctionField E.a₃) * h0 - 4 * e

noncomputable def invariantDifferential : Ω[E.toAffine.FunctionField⁄F] :=
  omegaAt E (genericPoint E)

theorem invariantDifferential_eq :
    invariantDifferential E = (2 * genY E + algebraMap F E.toAffine.FunctionField E.a₁ * genX E +
      algebraMap F E.toAffine.FunctionField E.a₃)⁻¹ • D F E.toAffine.FunctionField (genX E) := by
  have h := genDen_ne_zero E
  simp only [invariantDifferential, GroundTheory.Arith.Abelian.genericPoint, omegaAt]
  exact if_pos h

instance isSeparable_adjoin_genX :
    Algebra.IsSeparable F⟮genX E⟯ E.toAffine.FunctionField := by
  set F' := F⟮genX E⟯
  have sepX : IsSeparable F' (genX E) := by
    have : genX E = algebraMap F' E.toAffine.FunctionField
        ⟨genX E, IntermediateField.mem_adjoin_simple_self F _⟩ := rfl
    rw [this]
    exact isSeparable_algebraMap _
  have hAdj : F'⟮genX E⟯ = IntermediateField.extendScalars (le_refl F') := by
    apply IntermediateField.restrictScalars_injective F
    rw [IntermediateField.adjoin_simple_adjoin_simple, IntermediateField.extendScalars_restrictScalars,
      Set.pair_eq_singleton]
  have : Algebra.IsSeparable F' F'⟮genX E⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F' E.toAffine.FunctionField).mpr sepX
  have hY : IsSeparable F'⟮genX E⟯ (genY E) := by
    rw [hAdj]; exact isSeparable_genY E _ le_rfl
  have sepY : IsSeparable F' (genY E) := IsSeparable.of_algebra_isSeparable_of_isSeparable F' hY
  have := IntermediateField.isSeparable_adjoin_pair_of_isSeparable F' E.toAffine.FunctionField
    sepX sepY
  have hz : ∀ z : E.toAffine.FunctionField, z ∈ F'⟮genX E, genY E⟯ := by
    intro z
    have htop : (⊤ : IntermediateField F E.toAffine.FunctionField) ≤
        (F'⟮genX E, genY E⟯).restrictScalars F := by
      rw [← adjoin_genX_genY E, IntermediateField.restrictScalars_adjoin]
      exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_right
    exact htop trivial
  exact ⟨fun z => IntermediateField.isSeparable_of_mem_isSeparable F' E.toAffine.FunctionField (hz z)⟩

theorem D_genX_ne_zero : D F E.toAffine.FunctionField (genX E) ≠ 0 :=
  GroundTheory.Arith.SchemeCoh.D_ne_zero_of_isSeparable (genX E)

theorem invariantDifferential_ne_zero : invariantDifferential E ≠ 0 := by
  rw [invariantDifferential_eq]
  exact smul_ne_zero (inv_ne_zero (genDen_ne_zero E)) (D_genX_ne_zero E)

theorem span_invariantDifferential :
    Submodule.span E.toAffine.FunctionField {invariantDifferential E} = ⊤ := by
  rw [invariantDifferential_eq, Submodule.span_singleton_smul_eq
    (IsUnit.mk0 _ (inv_ne_zero (genDen_ne_zero E)))]
  exact GroundTheory.Arith.SchemeCoh.span_D_eq_top (genX E)

end Invariant

section Pullback

variable {F : Type u} [Field F] {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

noncomputable def isogenyPullback (φ : Isogeny E E') :
    Ω[E'.toAffine.FunctionField⁄F] →+ Ω[E.toAffine.FunctionField⁄F] :=
  kpush φ.comap

omit [E.IsElliptic] [E'.IsElliptic] in
theorem isogenyPullback_D (φ : Isogeny E E') (f : E'.toAffine.FunctionField) :
    isogenyPullback φ (D F _ f) = D F _ (φ.comap f) :=
  kpush_D _ _

omit [E.IsElliptic] [E'.IsElliptic] in
theorem isogenyPullback_smul (φ : Isogeny E E') (f : E'.toAffine.FunctionField)
    (η : Ω[E'.toAffine.FunctionField⁄F]) :
    isogenyPullback φ (f • η) = φ.comap f • isogenyPullback φ η :=
  kpush_smul _ _ _

theorem isogenyPullback_invariantDifferential (φ : Isogeny E E') :
    isogenyPullback φ (invariantDifferential E') = omegaAt E' φ.1 := by
  rw [isogenyPullback, invariantDifferential, kpush_omegaAt, φ.map_comap_genericPoint]

end Pullback

section Coefficient

variable {F : Type u} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

theorem mem_span_invariantDifferential (η : Ω[E.toAffine.FunctionField⁄F]) :
    η ∈ Submodule.span E.toAffine.FunctionField {invariantDifferential E} := by
  rw [span_invariantDifferential E]; trivial

noncomputable def invCoeff (η : Ω[E.toAffine.FunctionField⁄F]) : E.toAffine.FunctionField :=
  (Submodule.mem_span_singleton.mp (mem_span_invariantDifferential E η)).choose

theorem invCoeff_smul (η : Ω[E.toAffine.FunctionField⁄F]) :
    invCoeff E η • invariantDifferential E = η :=
  (Submodule.mem_span_singleton.mp (mem_span_invariantDifferential E η)).choose_spec

theorem invCoeff_eq {η : Ω[E.toAffine.FunctionField⁄F]} {c : E.toAffine.FunctionField}
    (h : c • invariantDifferential E = η) : invCoeff E η = c :=
  smul_left_injective _ (invariantDifferential_ne_zero E) ((invCoeff_smul E η).trans h.symm)

theorem invCoeff_add (η₁ η₂ : Ω[E.toAffine.FunctionField⁄F]) :
    invCoeff E (η₁ + η₂) = invCoeff E η₁ + invCoeff E η₂ :=
  invCoeff_eq E (by rw [add_smul, invCoeff_smul, invCoeff_smul])

theorem invCoeff_zero : invCoeff E 0 = 0 :=
  invCoeff_eq E (zero_smul _ _)

theorem invCoeff_invariantDifferential : invCoeff E (invariantDifferential E) = 1 :=
  invCoeff_eq E (one_smul _ _)

variable {E} {E' : WeierstrassCurve F} [E'.IsElliptic]

variable (E E') in

noncomputable def homCoeff : isogHom E E' →+ E.toAffine.FunctionField where
  toFun Q := invCoeff E (omegaAt E' Q.1)
  map_zero' := by
    show invCoeff E (omegaAt E' 0) = 0
    rw [omegaAt_zero, invCoeff_zero]
  map_add' Q₁ Q₂ := by
    show invCoeff E (omegaAt E' (Q₁.1 + Q₂.1)) = _
    rw [omegaAt_add, invCoeff_add]

omit [E'.IsElliptic] in
theorem homCoeff_smul (Q : isogHom E E') : homCoeff E E' Q • invariantDifferential E = omegaAt E' Q.1 :=
  invCoeff_smul E _

noncomputable def isogCoeff (φ : Isogeny E E') : E.toAffine.FunctionField :=
  homCoeff E E' ⟨φ.1, φ.respectsAdd⟩

theorem isogenyPullback_invariantDifferential_eq_smul (φ : Isogeny E E') :
    isogenyPullback φ (invariantDifferential E') = isogCoeff φ • invariantDifferential E := by
  rw [isogenyPullback_invariantDifferential, isogCoeff, homCoeff_smul]

theorem isogenyPullback_add {φ ψ χ : Isogeny E E'} (h : χ.1 = φ.1 + ψ.1) :
    isogenyPullback χ (invariantDifferential E') =
      isogenyPullback φ (invariantDifferential E') + isogenyPullback ψ (invariantDifferential E') := by
  rw [isogenyPullback_invariantDifferential, isogenyPullback_invariantDifferential,
    isogenyPullback_invariantDifferential, h, omegaAt_add]

theorem isogCoeff_add {φ ψ χ : Isogeny E E'} (h : χ.1 = φ.1 + ψ.1) :
    isogCoeff χ = isogCoeff φ + isogCoeff ψ := by
  have e : (⟨χ.1, χ.respectsAdd⟩ : isogHom E E') = ⟨φ.1, φ.respectsAdd⟩ + ⟨ψ.1, ψ.respectsAdd⟩ :=
    Subtype.ext h
  rw [isogCoeff, isogCoeff, isogCoeff, e, map_add]

variable (E) in

noncomputable def homIdentity : isogHom E E := ⟨genericPoint E, respectsAdd_genericPoint⟩

variable (E) in

theorem homCoeff_zsmul_homIdentity (n : ℤ) : homCoeff E E (n • homIdentity E) = n := by
  rw [map_zsmul]
  show n • invCoeff E (invariantDifferential E) = _
  rw [invCoeff_invariantDifferential, zsmul_one]

variable (E) in

theorem isogenyPullback_mulIsogeny (n : ℤ) (hn : n ≠ 0) :
    isogenyPullback (mulIsogeny E n hn) (invariantDifferential E) =
      (n : E.toAffine.FunctionField) • invariantDifferential E := by
  rw [isogenyPullback_invariantDifferential]
  show omegaAt E (n • genericPoint E) = _
  rw [omegaAt_zsmul, Int.cast_smul_eq_zsmul]
  rfl

variable (E) in
theorem isogCoeff_mulIsogeny (n : ℤ) (hn : n ≠ 0) : isogCoeff (mulIsogeny E n hn) = n :=
  homCoeff_zsmul_homIdentity E n

end Coefficient

end GroundTheory.Global
