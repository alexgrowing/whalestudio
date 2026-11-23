import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial

noncomputable section

def Scalable {𝒪 : Type*} [CommRing 𝒪] (π : 𝒪) (W : WeierstrassCurve 𝒪) : Prop :=
  π ∣ W.a₁ ∧ π ^ 2 ∣ W.a₂ ∧ π ^ 3 ∣ W.a₃ ∧ π ^ 4 ∣ W.a₄ ∧ π ^ 6 ∣ W.a₆

section Algebra

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (W : WeierstrassCurve 𝒪) {π : 𝒪}
  (hπ : Irreducible π)
include hπ

theorem pi_sq_dvd_y_of_double_root {A₁ A₂ A₃ A₄ A₆ : 𝒪} (h1 : W.a₁ = π * A₁) (h2 : W.a₂ = π * A₂)
    (h3 : W.a₃ = π ^ 2 * A₃) (h4 : W.a₄ = π ^ 2 * A₄) (h6 : W.a₆ = π ^ 3 * A₆) {x y X : 𝒪}
    (e : W.toAffine.Equation x y) (hx : x = π * X) (dy : π ∣ y) :
    π ^ 2 ∣ y ∧ π ∣ X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆ := by
  obtain ⟨Y, rfl⟩ := dy
  subst hx
  rw [equation_iff, h1, h2, h3, h4, h6] at e
  have hπ2 : π ^ 2 ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have hY : π ∣ Y ^ 2 := ⟨X ^ 3 + A₂ * X ^ 2 + A₄ * X + A₆ - A₁ * X * Y - A₃ * Y,
    mul_left_cancel₀ hπ2 (by linear_combination e)⟩
  obtain ⟨Y', rfl⟩ := hπ.prime.dvd_of_dvd_pow hY
  refine ⟨⟨Y', by ring⟩, Y' ^ 2 + A₁ * X * Y' + A₃ * Y', ?_⟩
  have hπ3 : π ^ 3 ≠ 0 := pow_ne_zero _ hπ.ne_zero
  exact mul_left_cancel₀ hπ3 (by linear_combination -e)

theorem variableChange_raises_divisibility {A₁ A₂ A₃ A₄ A₆ : 𝒪} (h1 : W.a₁ = π * A₁) (h2 : W.a₂ = π * A₂)
    (h3 : W.a₃ = π ^ 2 * A₃) (h4 : W.a₄ = π ^ 2 * A₄) (h6 : W.a₆ = π ^ 3 * A₆) {X₁ : 𝒪}
    (hP : π ∣ X₁ ^ 3 + A₂ * X₁ ^ 2 + A₄ * X₁ + A₆) (hD : π ∣ 3 * X₁ ^ 2 + 2 * A₂ * X₁ + A₄) :
    let W' := (⟨1, π * X₁, 0, 0⟩ : VariableChange 𝒪) • W
    π ∣ W'.a₁ ∧ π ∣ W'.a₂ ∧ π ^ 2 ∣ W'.a₃ ∧ π ^ 3 ∣ W'.a₄ ∧ π ^ 4 ∣ W'.a₆ := by
  intro W'
  simp only [W', variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul]
  obtain ⟨Z, hZ⟩ := hD
  obtain ⟨Z', hZ'⟩ := hP
  rw [h1, h2, h3, h4, h6]
  refine ⟨⟨A₁, by ring⟩, ⟨A₂ + 3 * X₁, by ring⟩, ⟨A₃ + X₁ * A₁, by ring⟩, ⟨Z, ?_⟩, ⟨Z', ?_⟩⟩
  · linear_combination π ^ 2 * hZ
  · linear_combination π ^ 3 * hZ'

theorem star_point (h1 : π ∣ W.a₁) (h2 : π ^ 2 ∣ W.a₂) {A₃ A₆ : 𝒪} (h3 : W.a₃ = π ^ 2 * A₃)
    (h4 : π ^ 3 ∣ W.a₄) (h6 : W.a₆ = π ^ 4 * A₆) {x y : 𝒪} (e : W.toAffine.Equation x y)
    (dx : π ∣ x) (dy : π ∣ y) :
    π ^ 2 ∣ x ∧ ∃ Y, y = π ^ 2 * Y ∧ π ∣ Y ^ 2 + A₃ * Y - A₆ := by
  obtain ⟨A₁, hA₁⟩ := h1
  obtain ⟨B₂, hB₂⟩ := h2
  obtain ⟨B₄, hB₄⟩ := h4
  obtain ⟨X, rfl⟩ := dx
  obtain ⟨hy2, hP⟩ := pi_sq_dvd_y_of_double_root W hπ hA₁ (A₂ := π * B₂) (by rw [hB₂]; ring) h3
    (A₄ := π * B₄) (by rw [hB₄]; ring) (A₆ := π * A₆) (by rw [h6]; ring) e rfl dy
  have hX : π ∣ X := by
    apply hπ.prime.dvd_of_dvd_pow (n := 3)
    obtain ⟨c, hc⟩ := hP
    exact ⟨c - B₂ * X ^ 2 - B₄ * X - A₆, by linear_combination hc⟩
  obtain ⟨X', rfl⟩ := hX
  obtain ⟨Y, rfl⟩ := hy2
  refine ⟨⟨X', by ring⟩, Y, rfl, ?_⟩
  rw [equation_iff, hA₁, hB₂, h3, hB₄, h6] at e
  have hπ4 : π ^ 4 ≠ 0 := pow_ne_zero _ hπ.ne_zero
  exact ⟨π * X' ^ 3 + π * B₂ * X' ^ 2 + B₄ * X' - A₁ * X' * Y,
    mul_left_cancel₀ hπ4 (by linear_combination e)⟩

theorem vc_star_step (h1 : π ∣ W.a₁) (h2 : π ^ 2 ∣ W.a₂) {A₃ A₆ : 𝒪} (h3 : W.a₃ = π ^ 2 * A₃)
    (h4 : π ^ 3 ∣ W.a₄) (h6 : W.a₆ = π ^ 4 * A₆) {Y₁ : 𝒪} (hQ : π ∣ Y₁ ^ 2 + A₃ * Y₁ - A₆)
    (hD : π ∣ 2 * Y₁ + A₃) :
    let W' := (⟨1, 0, 0, π ^ 2 * Y₁⟩ : VariableChange 𝒪) • W
    π ∣ W'.a₁ ∧ π ^ 2 ∣ W'.a₂ ∧ π ^ 3 ∣ W'.a₃ ∧ π ^ 3 ∣ W'.a₄ ∧ π ^ 5 ∣ W'.a₆ := by
  intro W'
  simp only [W', variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul]
  obtain ⟨A₁, hA₁⟩ := h1
  obtain ⟨B₂, hB₂⟩ := h2
  obtain ⟨B₄, hB₄⟩ := h4
  obtain ⟨Z, hZ⟩ := hD
  obtain ⟨Z', hZ'⟩ := hQ
  rw [hA₁, hB₂, h3, hB₄, h6]
  refine ⟨⟨A₁, by ring⟩, ⟨B₂, by ring⟩, ⟨Z, ?_⟩, ⟨B₄ - Y₁ * A₁, by ring⟩, ⟨-Z', ?_⟩⟩
  · linear_combination π ^ 2 * hZ
  · linear_combination (-π ^ 4) * hZ'

theorem pi_sq_dvd_x_of_normal_form (h1 : π ∣ W.a₁) (h2 : π ^ 2 ∣ W.a₂) (h3 : π ^ 3 ∣ W.a₃) (h4 : π ^ 3 ∣ W.a₄)
    (h6 : π ^ 5 ∣ W.a₆) {x y : 𝒪} (e : W.toAffine.Equation x y) (dx : π ∣ x) (dy : π ∣ y) :
    π ^ 2 ∣ x ∧ π ^ 3 ∣ y := by
  obtain ⟨B₃, hB₃⟩ := h3
  obtain ⟨B₆, hB₆⟩ := h6
  obtain ⟨hx, Y, rfl, hQ⟩ := star_point W hπ h1 h2 (A₃ := π * B₃) (by rw [hB₃]; ring) h4
    (A₆ := π * B₆) (by rw [hB₆]; ring) e dx dy
  refine ⟨hx, ?_⟩
  have hY : π ∣ Y := by
    apply hπ.prime.dvd_of_dvd_pow (n := 2)
    obtain ⟨c, hc⟩ := hQ
    exact ⟨c - B₃ * Y + B₆, by linear_combination hc⟩
  obtain ⟨Y', rfl⟩ := hY
  exact ⟨Y', by ring⟩

end Algebra

section Bound

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] {π : 𝒪} (hπ : Irreducible π)
include hπ

local notation "ι" => algebraMap 𝒪 K

theorem knBound_I0star {A₁ A₂ A₃ A₄ A₆ : 𝒪} (h1 : W.a₁ = π * A₁) (h2 : W.a₂ = π * A₂)
    (h3 : W.a₃ = π ^ 2 * A₃) (h4 : W.a₄ = π ^ 2 * A₄) (h6 : W.a₆ = π ^ 3 * A₆)
    (hD : ∀ x y X : 𝒪, W.toAffine.Equation x y → x = π * X → π ∣ y →
      ¬π ∣ 3 * X ^ 2 + 2 * A₂ * X + A₄) :
    KNBound K W 4 := by
  have d1 : π ∣ W.a₁ := ⟨A₁, h1⟩
  have d2 : π ∣ W.a₂ := ⟨A₂, h2⟩
  have d3 : π ∣ W.a₃ := ⟨π * A₃, by rw [h3]; ring⟩
  have d4 : π ∣ W.a₄ := ⟨π * A₄, by rw [h4]; ring⟩
  have d6 : π ∣ W.a₆ := ⟨π ^ 2 * A₆, by rw [h6]; ring⟩
  have hcard := card_cubicRoots (a := (1 : ResidueField 𝒪)) (b := residue 𝒪 A₂)
    (c := residue 𝒪 A₄) (d := residue 𝒪 A₆) one_ne_zero
  refine (knBound_of_rel K W (cubicRoots 1 (residue 𝒪 A₂) (residue 𝒪 A₄) (residue 𝒪 A₆))
    (fun P c => ∃ (x y X : 𝒪) (h : (curveK K W).Nonsingular (ι x) (ι y)),
      P = Point.some _ _ h ∧ x = π * X ∧ π ∣ y ∧ residue 𝒪 X = c) ?_ ?_).mono K (by omega)
  · intro P hP
    obtain ⟨x, y, h, rfl, e, ⟨X, rfl⟩, dy⟩ := exists_of_notMem_E0Set K W hπ d3 d4 d6 hP
    refine ⟨residue 𝒪 X, mem_cubicRoots one_ne_zero ?_, π * X, y, X, h, rfl, rfl, dy, rfl⟩
    have := (dvd_iff_residue_eq_zero hπ).1 (pi_sq_dvd_y_of_double_root W hπ h1 h2 h3 h4 h6 e rfl dy).2
    simp only [map_add, map_mul, map_pow] at this
    linear_combination this
  · rintro P Q c hP hQ ⟨x, y, X, h, rfl, rfl, dy, rfl⟩ ⟨x', y', X', h', rfl, rfl, dy', hc⟩
    by_contra hPQ
    obtain ⟨hn, hneg⟩ := neg_some_integral K W h'
    have hR := sub_notMem_E0Set K W hPQ
    have hQ' := neg_notMem_E0Set K W hQ
    rw [hneg] at hQ'
    obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, ⟨g₁, e₁⟩, ⟨g₂, e₂⟩, -, -, -, -, -, -, -, -, ⟨X₃, rfl⟩,
      -, ⟨L, rfl⟩, -, l1, -, -, v1, v2, -⟩ := triple_cusp K W hπ d1 d2 d3 d4 d6 hP hQ' hR
        (by rw [← hneg]; abel)
    obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₁
    obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₂
    have ey := equation_of_map K W h.1
    obtain ⟨hy2, -⟩ := pi_sq_dvd_y_of_double_root W hπ h1 h2 h3 h4 h6 ey rfl dy
    obtain ⟨Y, rfl⟩ := hy2
    have hν : ν = π ^ 2 * (Y - L * X) := by linear_combination -l1
    subst hν
    rw [h1, h2] at v1
    rw [h1, h3, h4] at v2
    have hπ0 := hπ.ne_zero
    have s1 : π ∣ X + X' + X₃ + A₂ := ⟨L ^ 2 + A₁ * L, mul_left_cancel₀ hπ0 (by linear_combination v1)⟩
    have s2 : π ∣ X * X' + X * X₃ + X' * X₃ - A₄ :=
      ⟨-2 * L * (Y - L * X) - A₁ * (Y - L * X) - A₃ * L,
        mul_left_cancel₀ (pow_ne_zero 2 hπ0) (by linear_combination v2)⟩
    have s0 : π ∣ X - X' := by
      rw [dvd_iff_residue_eq_zero hπ, map_sub, hc, sub_self]
    apply hD (π * X) (π ^ 2 * Y) X ey rfl ⟨π * Y, by ring⟩
    have := dvd_sub (dvd_add (dvd_mul_of_dvd_left s0 (X - X₃)) (dvd_mul_of_dvd_right s1 (2 * X))) s2
    convert this using 1; ring

theorem knBound_IVstar (h1 : π ∣ W.a₁) (h2 : π ^ 2 ∣ W.a₂) {A₃ A₆ : 𝒪} (h3 : W.a₃ = π ^ 2 * A₃)
    (h4 : π ^ 3 ∣ W.a₄) (h6 : W.a₆ = π ^ 4 * A₆)
    (hD : ∀ x y Y : 𝒪, W.toAffine.Equation x y → π ∣ x → y = π ^ 2 * Y → ¬π ∣ 2 * Y + A₃) :
    KNBound K W 3 := by
  have d2 : π ∣ W.a₂ := (dvd_pow_self π two_ne_zero).trans h2
  have d3 : π ∣ W.a₃ := ⟨π * A₃, by rw [h3]; ring⟩
  have d4 : π ∣ W.a₄ := (dvd_pow_self π three_ne_zero).trans h4
  have d6 : π ∣ W.a₆ := ⟨π ^ 3 * A₆, by rw [h6]; ring⟩
  have hcard := card_quadRoots (a := (1 : ResidueField 𝒪)) (b := residue 𝒪 A₃)
    (c := -residue 𝒪 A₆) one_ne_zero
  refine (knBound_of_rel K W (quadRoots 1 (residue 𝒪 A₃) (-residue 𝒪 A₆))
    (fun P c => ∃ (x y Y : 𝒪) (h : (curveK K W).Nonsingular (ι x) (ι y)),
      P = Point.some _ _ h ∧ π ∣ x ∧ y = π ^ 2 * Y ∧ residue 𝒪 Y = c) ?_ ?_).mono K (by omega)
  · intro P hP
    obtain ⟨x, y, h, rfl, e, dx, dy⟩ := exists_of_notMem_E0Set K W hπ d3 d4 d6 hP
    obtain ⟨-, Y, rfl, hQ⟩ := star_point W hπ h1 h2 h3 h4 h6 e dx dy
    refine ⟨residue 𝒪 Y, mem_quadRoots one_ne_zero ?_, x, π ^ 2 * Y, Y, h, rfl, dx, rfl, rfl⟩
    have := (dvd_iff_residue_eq_zero hπ).1 hQ
    simp only [map_sub, map_add, map_mul, map_pow] at this
    linear_combination this
  · rintro P Q c hP hQ ⟨x, y, Y, h, rfl, dx, rfl, rfl⟩ ⟨x', y', Y', h', rfl, dx', rfl, hc⟩
    by_contra hPQ
    obtain ⟨hn, hneg⟩ := neg_some_integral K W h'
    have hR := sub_notMem_E0Set K W hPQ
    have hQ' := neg_notMem_E0Set K W hQ
    rw [hneg] at hQ'
    obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, ⟨g₁, e₁⟩, ⟨g₂, e₂⟩, -, -, -, -, -, -, -, -, -, -,
      ⟨L, rfl⟩, -, l1, l2, -, -, -, -⟩ := triple_cusp K W hπ h1 d2 d3 d4 d6 hP hQ' hR
        (by rw [← hneg]; abel)
    obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₁
    obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₂
    have ey := equation_of_map K W h.1
    have ey' := equation_of_map K W h'.1
    obtain ⟨⟨X, rfl⟩, -⟩ := star_point W hπ h1 h2 h3 h4 h6 ey dx ⟨π * Y, by ring⟩
    obtain ⟨⟨X', rfl⟩, -⟩ := star_point W hπ h1 h2 h3 h4 h6 ey' dx' ⟨π * Y', by ring⟩
    obtain ⟨A₁, hA₁⟩ := h1
    have hc' : π ∣ Y - Y' := by
      rw [dvd_iff_residue_eq_zero hπ, map_sub, hc, sub_self]
    apply hD _ _ Y ey dx rfl
    rw [hA₁, h3] at l2
    have key : π ^ 2 * (Y + Y' + A₃) = π ^ 2 * (π * (L * (X - X') - A₁ * X')) := by
      linear_combination l1 - l2
    have h5 : π ∣ Y + Y' + A₃ := ⟨_, mul_left_cancel₀ (pow_ne_zero 2 hπ.ne_zero) key⟩
    have := dvd_add h5 hc'
    convert this using 1
    ring

theorem kodairaNeron_bound_IIIstar_IIstar (h1 : π ∣ W.a₁) (h2 : π ^ 2 ∣ W.a₂) (h3 : π ^ 3 ∣ W.a₃) (h4 : π ^ 3 ∣ W.a₄)
    (h6 : π ^ 5 ∣ W.a₆) (hmin : ¬Scalable π W) : KNBound K W 2 := by
  have d2 : π ∣ W.a₂ := (dvd_pow_self π two_ne_zero).trans h2
  have d3 : π ∣ W.a₃ := (dvd_pow_self π three_ne_zero).trans h3
  have d4 : π ∣ W.a₄ := (dvd_pow_self π three_ne_zero).trans h4
  have d6 : π ∣ W.a₆ := (dvd_pow_self π (by norm_num : 5 ≠ 0)).trans h6
  by_cases h4' : π ^ 4 ∣ W.a₄
  · by_cases h6' : π ^ 6 ∣ W.a₆
    · exact absurd ⟨h1, h2, h3, h4', h6'⟩ hmin
    · refine (knBound_one K W fun P => ?_).mono K (by norm_num)
      by_contra hP
      obtain ⟨x, y, h, rfl, e, dx, dy⟩ := exists_of_notMem_E0Set K W hπ d3 d4 d6 hP
      obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := pi_sq_dvd_x_of_normal_form W hπ h1 h2 h3 h4 h6 e dx dy
      apply h6'
      obtain ⟨A₁, hA₁⟩ := h1
      obtain ⟨B₂, hB₂⟩ := h2
      obtain ⟨B₃, hB₃⟩ := h3
      obtain ⟨B₄, hB₄⟩ := h4'
      rw [equation_iff, hA₁, hB₂, hB₃, hB₄] at e
      exact ⟨Y ^ 2 + A₁ * X * Y + B₃ * Y - X ^ 3 - B₂ * X ^ 2 - B₄ * X, by linear_combination -e⟩
  · refine knBound_two K W fun P Q R hP hQ hR hs => ?_
    obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, -, -, -, e₁, e₂, e₃, dx₁, dy₁, dx₂, dy₂, dx₃, dy₃,
      ⟨L, rfl⟩, -, l1, -, -, -, v2, -⟩ := triple_cusp K W hπ h1 d2 d3 d4 d6 hP hQ hR hs
    obtain ⟨⟨X₁, rfl⟩, ⟨Y₁, rfl⟩⟩ := pi_sq_dvd_x_of_normal_form W hπ h1 h2 h3 h4 h6 e₁ dx₁ dy₁
    obtain ⟨⟨X₂, rfl⟩, -⟩ := pi_sq_dvd_x_of_normal_form W hπ h1 h2 h3 h4 h6 e₂ dx₂ dy₂
    obtain ⟨⟨X₃, rfl⟩, -⟩ := pi_sq_dvd_x_of_normal_form W hπ h1 h2 h3 h4 h6 e₃ dx₃ dy₃
    have hν : ν = π ^ 3 * (Y₁ - L * X₁) := by linear_combination -l1
    subst hν
    obtain ⟨A₁, hA₁⟩ := h1
    obtain ⟨B₃, hB₃⟩ := h3
    apply h4'
    rw [hA₁, hB₃] at v2
    exact ⟨X₁ * X₂ + X₁ * X₃ + X₂ * X₃ + 2 * L * (Y₁ - L * X₁) + A₁ * (Y₁ - L * X₁) + B₃ * L,
      by linear_combination -v2⟩

theorem knBound_star (h1 : π ∣ W.a₁) (h2 : π ^ 2 ∣ W.a₂) {A₃ A₆ : 𝒪} (h3 : W.a₃ = π ^ 2 * A₃)
    (h4 : π ^ 3 ∣ W.a₄) (h6 : W.a₆ = π ^ 4 * A₆)
    (hmin : ∀ C : VariableChange 𝒪, ¬Scalable π (C • W)) : KNBound K W 3 := by
  by_cases hex : ∃ x y Y : 𝒪, W.toAffine.Equation x y ∧ π ∣ x ∧ y = π ^ 2 * Y ∧ π ∣ 2 * Y + A₃
  · obtain ⟨x, y, Y, e, dx, rfl, hD⟩ := hex
    obtain ⟨-, Y', hY', hQ⟩ := star_point W hπ h1 h2 h3 h4 h6 e dx ⟨π * Y, by ring⟩
    have hYY : Y' = Y := mul_left_cancel₀ (pow_ne_zero 2 hπ.ne_zero) hY'.symm
    subst hYY
    obtain ⟨s1, s2, s3, s4, s6⟩ := vc_star_step W hπ h1 h2 h3 h4 h6 hQ hD
    refine (KNBound.of_vc K W ⟨1, 0, 0, π ^ 2 * Y'⟩ ?_).mono K (by norm_num : 2 ≤ 3)
    exact kodairaNeron_bound_IIIstar_IIstar K _ hπ s1 s2 s3 s4 s6 (hmin _)
  · push Not at hex
    exact knBound_IVstar K W hπ h1 h2 h3 h4 h6 fun x y Y e dx hy hD => hex x y Y e dx hy hD

end Bound

end

end GroundTheory.Arith.Abelian
