import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronStar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial

noncomputable section

def StageY {𝒪 : Type*} [CommRing 𝒪] (π : 𝒪) (j : ℕ) (W : WeierstrassCurve 𝒪) : Prop :=
  π ∣ W.a₁ ∧ (∃ A₂, W.a₂ = π * A₂ ∧ ¬π ∣ A₂) ∧ π ^ j ∣ W.a₃ ∧ π ^ (j + 1) ∣ W.a₄ ∧
    π ^ (2 * j) ∣ W.a₆

def StageX {𝒪 : Type*} [CommRing 𝒪] (π : 𝒪) (j : ℕ) (W : WeierstrassCurve 𝒪) : Prop :=
  π ∣ W.a₁ ∧ (∃ A₂, W.a₂ = π * A₂ ∧ ¬π ∣ A₂) ∧ π ^ (j + 1) ∣ W.a₃ ∧ π ^ (j + 1) ∣ W.a₄ ∧
    π ^ (2 * j + 1) ∣ W.a₆

section Algebra

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪) {π : 𝒪} (hπ : Irreducible π)
include hπ

theorem StageX.stageY {j : ℕ} (h : StageX π j W) : StageY π j W :=
  ⟨h.1, h.2.1, (pow_dvd_pow π (by omega)).trans h.2.2.1, h.2.2.2.1,
    (pow_dvd_pow π (by omega)).trans h.2.2.2.2⟩

theorem deep_step {j m : ℕ} (hm : m + 1 ≤ j) (hS : StageY π j W) {X Y : 𝒪}
    (e : W.toAffine.Equation (π ^ m * X) (π ^ m * Y)) (hX3 : π ^ 2 ∣ π ^ m * X ^ 3) :
    π ∣ X ∧ π ∣ Y := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂, hA₂'⟩, h3, h4, h6⟩ := hS
  obtain ⟨B₃, hB₃⟩ := (pow_dvd_pow π (by omega : m + 1 ≤ j)).trans h3
  obtain ⟨B₄, hB₄⟩ := (pow_dvd_pow π (by omega : m + 2 ≤ j + 1)).trans h4
  obtain ⟨B₆, hB₆⟩ := (pow_dvd_pow π (by omega : 2 * m + 2 ≤ 2 * j)).trans h6
  obtain ⟨c, hc⟩ := hX3
  rw [equation_iff, hA₁, hA₂, hB₃, hB₄, hB₆] at e
  have hπm : π ^ (2 * m) ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have hY : π ∣ Y ^ 2 := ⟨-A₁ * X * Y - B₃ * Y + π * c + A₂ * X ^ 2 + π * B₄ * X + π * B₆,
    mul_left_cancel₀ hπm (by linear_combination e + π ^ (2 * m) * hc)⟩
  obtain ⟨Y', rfl⟩ := hπ.prime.dvd_of_dvd_pow hY
  refine ⟨?_, dvd_mul_right _ _⟩
  have hπm1 : π ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have hAX : π ∣ A₂ * X ^ 2 := ⟨Y' ^ 2 + A₁ * X * Y' + B₃ * Y' - c - B₄ * X - B₆,
    mul_left_cancel₀ hπm1 (by linear_combination -e - π ^ (2 * m) * hc)⟩
  rcases hπ.prime.dvd_or_dvd hAX with h | h
  · exact absurd h hA₂'
  · exact hπ.prime.dvd_of_dvd_pow h

theorem stageY_deep {j : ℕ} (hj : 2 ≤ j) (hS : StageY π j W) {x y : 𝒪}
    (e : W.toAffine.Equation x y) (hx : π ^ 2 ∣ x) (hy : π ∣ y) : π ^ j ∣ x ∧ π ^ j ∣ y := by
  have key : ∀ m, 1 ≤ m → m ≤ j → π ^ m ∣ x ∧ π ^ m ∣ y := by
    intro m hm1
    induction m, hm1 using Nat.le_induction with
    | base => exact fun _ => ⟨by simpa using (dvd_pow_self π two_ne_zero).trans hx, by simpa using hy⟩
    | succ m hm ih =>
      intro hmj
      obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := ih (by omega)
      have hX3 : π ^ 2 ∣ π ^ m * X ^ 3 := by
        rcases Nat.lt_or_ge m 2 with hm2 | hm2
        · obtain rfl : m = 1 := by omega
          have hX : π ∣ X := by
            obtain ⟨c, hc⟩ := hx
            exact ⟨c, mul_left_cancel₀ hπ.ne_zero (by linear_combination hc)⟩
          obtain ⟨X', rfl⟩ := hX
          exact ⟨X' ^ 3 * π ^ 2, by ring⟩
        · exact dvd_mul_of_dvd_left (pow_dvd_pow π hm2) _
      obtain ⟨⟨X', rfl⟩, ⟨Y', rfl⟩⟩ := deep_step W hπ hmj hS e hX3
      exact ⟨⟨X', by ring⟩, ⟨Y', by ring⟩⟩
  exact key j (by omega) le_rfl

theorem stageY_quad {j : ℕ} (hj : 1 ≤ j) (hS : StageY π j W) {A₃ A₆ : 𝒪} (h3 : W.a₃ = π ^ j * A₃)
    (h6 : W.a₆ = π ^ (2 * j) * A₆) {X Y : 𝒪} (e : W.toAffine.Equation (π ^ j * X) (π ^ j * Y)) :
    π ∣ Y ^ 2 + A₃ * Y - A₆ := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂, -⟩, -, ⟨B₄, hB₄⟩, -⟩ := hS
  rw [equation_iff, hA₁, hA₂, h3, hB₄, h6] at e
  have hπm : π ^ (2 * (i + 1)) ≠ 0 := pow_ne_zero _ hπ.ne_zero
  exact ⟨-A₁ * X * Y + π ^ i * X ^ 3 + A₂ * X ^ 2 + B₄ * X,
    mul_left_cancel₀ hπm (by linear_combination e)⟩

theorem stageX_deep {j : ℕ} (hj : 2 ≤ j) (hS : StageX π j W) {x y : 𝒪}
    (e : W.toAffine.Equation x y) (hx : π ^ 2 ∣ x) (hy : π ∣ y) : π ^ j ∣ x ∧ π ^ (j + 1) ∣ y := by
  obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := stageY_deep W hπ hj (hS.stageY W hπ) e hx hy
  refine ⟨dvd_mul_right _ _, ?_⟩
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂, -⟩, ⟨B₃, hB₃⟩, ⟨B₄, hB₄⟩, ⟨B₆, hB₆⟩⟩ := hS
  rw [equation_iff, hA₁, hA₂, hB₃, hB₄, hB₆] at e
  have hπm : π ^ (2 * j) ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have hY : π ∣ Y ^ 2 := ⟨-A₁ * X * Y - B₃ * Y + π ^ (j - 1) * X ^ 3 + A₂ * X ^ 2 + B₄ * X + B₆,
    mul_left_cancel₀ hπm (by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      linear_combination e)⟩
  obtain ⟨Y', rfl⟩ := hπ.prime.dvd_of_dvd_pow hY
  exact ⟨Y', by ring⟩

theorem stageX_quad {j : ℕ} (hj : 2 ≤ j) (hS : StageX π j W) {A₂ A₄ A₆ : 𝒪}
    (h2 : W.a₂ = π * A₂) (h4 : W.a₄ = π ^ (j + 1) * A₄) (h6 : W.a₆ = π ^ (2 * j + 1) * A₆)
    {X Y : 𝒪} (e : W.toAffine.Equation (π ^ j * X) (π ^ (j + 1) * Y)) :
    π ∣ A₂ * X ^ 2 + A₄ * X + A₆ := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  obtain ⟨⟨A₁, hA₁⟩, -, ⟨B₃, hB₃⟩, -, -⟩ := hS
  rw [equation_iff, hA₁, h2, hB₃, h4, h6] at e
  have hπm : π ^ (2 * (i + 2) + 1) ≠ 0 := pow_ne_zero _ hπ.ne_zero
  exact ⟨Y ^ 2 + A₁ * X * Y + B₃ * Y - π ^ i * X ^ 3,
    mul_left_cancel₀ hπm (by linear_combination -e)⟩

theorem vc_stageY_step {j : ℕ} (hS : StageY π j W) {A₃ A₆ : 𝒪} (h3 : W.a₃ = π ^ j * A₃)
    (h6 : W.a₆ = π ^ (2 * j) * A₆) {Y₁ : 𝒪} (hQ : π ∣ Y₁ ^ 2 + A₃ * Y₁ - A₆)
    (hD : π ∣ 2 * Y₁ + A₃) : StageX π j ((⟨1, 0, 0, π ^ j * Y₁⟩ : VariableChange 𝒪) • W) := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂, hA₂'⟩, -, ⟨B₄, hB₄⟩, -⟩ := hS
  obtain ⟨Z, hZ⟩ := hD
  obtain ⟨Z', hZ'⟩ := hQ
  simp only [StageX, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul]
  rw [hA₁, hA₂, h3, hB₄, h6]
  refine ⟨⟨A₁, by ring⟩, ⟨A₂, by ring, hA₂'⟩, ⟨Z, ?_⟩, ⟨B₄ - Y₁ * A₁, by ring⟩, ⟨-Z', ?_⟩⟩
  · linear_combination π ^ j * hZ
  · linear_combination (-π ^ (2 * j)) * hZ'

theorem vc_stageX_step {j : ℕ} (hj : 2 ≤ j) (hS : StageX π j W) {A₂ A₄ A₆ : 𝒪}
    (h2 : W.a₂ = π * A₂) (h4 : W.a₄ = π ^ (j + 1) * A₄) (h6 : W.a₆ = π ^ (2 * j + 1) * A₆)
    {X₁ : 𝒪} (hQ : π ∣ A₂ * X₁ ^ 2 + A₄ * X₁ + A₆) (hD : π ∣ 2 * A₂ * X₁ + A₄) :
    StageY π (j + 1) ((⟨1, π ^ j * X₁, 0, 0⟩ : VariableChange 𝒪) • W) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂', hA₂', hA₂''⟩, ⟨B₃, hB₃⟩, -, -⟩ := hS
  have hAA : A₂' = A₂ := mul_left_cancel₀ hπ.ne_zero (hA₂'.symm.trans h2)
  subst hAA
  obtain ⟨Z, hZ⟩ := hD
  obtain ⟨Z', hZ'⟩ := hQ
  simp only [StageY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul]
  rw [hA₁, h2, hB₃, h4, h6]
  refine ⟨⟨A₁, by ring⟩, ⟨A₂' + 3 * π ^ (i + 1) * X₁, by ring, ?_⟩, ⟨B₃ + X₁ * A₁, by ring⟩,
    ⟨Z + 3 * π ^ i * X₁ ^ 2, ?_⟩, ⟨Z' + π ^ i * X₁ ^ 3, ?_⟩⟩
  · intro h
    apply hA₂''
    have := dvd_sub h (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self π
      (Nat.succ_ne_zero i)) 3) X₁)
    simpa using this
  · linear_combination π ^ (i + 3) * hZ
  · linear_combination π ^ (2 * (i + 2) + 1) * hZ'

theorem stageY_dvd_Δ {i : ℕ} (hS : StageY π (i + 2) W) : π ^ (2 * i + 7) ∣ W.Δ := by
  obtain ⟨⟨A₁, hA₁⟩, ⟨A₂, hA₂, -⟩, ⟨B₃, hB₃⟩, ⟨B₄, hB₄⟩, ⟨B₆, hB₆⟩⟩ := hS
  set c₂ := π * A₁ ^ 2 + 4 * A₂
  set c₄ := 2 * B₄ + A₁ * B₃
  set c₆ := B₃ ^ 2 + 4 * B₆
  set c₈ := π * A₁ ^ 2 * B₆ + 4 * A₂ * B₆ - π * A₁ * B₃ * B₄ + A₂ * B₃ ^ 2 - π * B₄ ^ 2
  have e2 : W.b₂ = π * c₂ := by
    rw [WeierstrassCurve.b₂, hA₁, hA₂]; ring
  have e4 : W.b₄ = π ^ (i + 3) * c₄ := by
    rw [WeierstrassCurve.b₄, hA₁, hB₃, hB₄]; ring
  have e6 : W.b₆ = π ^ (2 * i + 4) * c₆ := by
    rw [WeierstrassCurve.b₆, hB₃, hB₆]; ring
  have e8 : W.b₈ = π ^ (2 * i + 5) * c₈ := by
    rw [WeierstrassCurve.b₈, hA₁, hA₂, hB₃, hB₄, hB₆]; ring
  rw [WeierstrassCurve.Δ, e2, e4, e6, e8]
  exact ⟨-c₂ ^ 2 * c₈ - 8 * π ^ (i + 2) * c₄ ^ 3 - 27 * π ^ (2 * i + 1) * c₆ ^ 2 +
    9 * π ^ (i + 1) * c₂ * c₄ * c₆, by ring⟩

end Algebra

section Bound

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] {π : 𝒪} (hπ : Irreducible π)
include hπ

local notation "ι" => algebraMap 𝒪 K

theorem two_not_deep {X₁ X₂ X₃ : 𝒪} (hX₁ : ¬π ∣ X₁) (hX₂ : ¬π ∣ X₂)
    (s2 : π ∣ X₁ * X₂ + X₁ * X₃ + X₂ * X₃) (s3 : π ∣ X₁ * X₂ * X₃) : False := by
  have hX₃ : π ∣ X₃ := by
    rcases hπ.prime.dvd_or_dvd s3 with h | h
    · rcases hπ.prime.dvd_or_dvd h with h' | h'
      · exact absurd h' hX₁
      · exact absurd h' hX₂
    · exact h
  have : π ∣ X₁ * X₂ := by
    have := dvd_sub s2 (dvd_mul_of_dvd_right hX₃ (X₁ + X₂))
    convert this using 1; ring
  rcases hπ.prime.dvd_or_dvd this with h | h
  · exact hX₁ h
  · exact hX₂ h

omit [IsDiscreteValuationRing 𝒪] in
theorem not_dvd_of_not_sq_dvd {X : 𝒪} (h : ¬π ^ 2 ∣ π * X) : ¬π ∣ X := by
  rintro ⟨c, rfl⟩; exact h ⟨c, by ring⟩

theorem exists_integral_coords_of_sum_zero (h1 : π ∣ W.a₁) {A₂ : 𝒪} (h2 : W.a₂ = π * A₂) (h3 : π ^ 2 ∣ W.a₃)
    (h4 : π ^ 3 ∣ W.a₄) (h6 : π ^ 4 ∣ W.a₆) {P₁ P₂ P₃ : (curveK K W).Point}
    (hP₁ : P₁ ∉ E0Set K W) (hP₂ : P₂ ∉ E0Set K W) (hP₃ : P₃ ∉ E0Set K W)
    (hs : P₁ + P₂ + P₃ = 0) :
    ∃ X₁ y₁ X₂ y₂ X₃ y₃ : 𝒪, (∃ h, P₁ = Point.some (ι (π * X₁)) (ι y₁) h) ∧
      (∃ h, P₂ = Point.some (ι (π * X₂)) (ι y₂) h) ∧ (∃ h, P₃ = Point.some (ι (π * X₃)) (ι y₃) h) ∧
      π ∣ X₁ + X₂ + X₃ + A₂ ∧ π ∣ X₁ * X₂ + X₁ * X₃ + X₂ * X₃ ∧ π ∣ X₁ * X₂ * X₃ := by
  have d2 : π ∣ W.a₂ := ⟨A₂, h2⟩
  have d3 : π ∣ W.a₃ := (dvd_pow_self π two_ne_zero).trans h3
  have d4 : π ∣ W.a₄ := (dvd_pow_self π three_ne_zero).trans h4
  have d6 : π ∣ W.a₆ := (dvd_pow_self π four_ne_zero).trans h6
  obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, p₁, p₂, p₃, e₁, e₂, e₃, ⟨X₁, rfl⟩, dy₁, ⟨X₂, rfl⟩, -,
    ⟨X₃, rfl⟩, -, ⟨L, rfl⟩, -, l1, -, -, v1, v2, v3⟩ :=
    triple_cusp K W hπ h1 d2 d3 d4 d6 hP₁ hP₂ hP₃ hs
  obtain ⟨A₁, hA₁⟩ := h1
  obtain ⟨B₃, hB₃⟩ := h3
  obtain ⟨B₄, hB₄⟩ := h4
  obtain ⟨B₆, hB₆⟩ := h6
  obtain ⟨⟨Y₁, rfl⟩, -⟩ := pi_sq_dvd_y_of_double_root W hπ hA₁ h2 hB₃ (A₄ := π * B₄) (by rw [hB₄]; ring)
    (A₆ := π * B₆) (by rw [hB₆]; ring) e₁ rfl dy₁
  have hν : ν = π ^ 2 * (Y₁ - L * X₁) := by linear_combination -l1
  subst hν
  rw [hA₁, h2] at v1
  rw [hA₁, hB₃, hB₄] at v2
  rw [hB₃, hB₆] at v3
  have hπ0 := hπ.ne_zero
  refine ⟨X₁, _, X₂, y₂, X₃, y₃, p₁, p₂, p₃,
    ⟨L ^ 2 + A₁ * L, mul_left_cancel₀ hπ0 (by linear_combination v1)⟩,
    ⟨B₄ - 2 * L * (Y₁ - L * X₁) - A₁ * (Y₁ - L * X₁) - B₃ * L,
      mul_left_cancel₀ (pow_ne_zero 2 hπ0) (by linear_combination v2)⟩,
    ⟨(Y₁ - L * X₁) ^ 2 + B₃ * (Y₁ - L * X₁) - B₆,
      mul_left_cancel₀ (pow_ne_zero 3 hπ0) (by linear_combination v3)⟩⟩

theorem kodairaNeron_bound_of_double_root_y {j : ℕ} (hj : 2 ≤ j) (hS : StageY π j W) {A₃ A₆ : 𝒪}
    (h3 : W.a₃ = π ^ j * A₃) (h6 : W.a₆ = π ^ (2 * j) * A₆)
    (hD : ∀ x y Y : 𝒪, W.toAffine.Equation x y → π ^ 2 ∣ x → y = π ^ j * Y →
      ¬π ∣ 2 * Y + A₃) :
    KNBound K W 4 := by
  obtain ⟨d1, ⟨A₂, h2, hA₂⟩, -, h4, -⟩ := hS
  have d3 : π ^ 2 ∣ W.a₃ := ⟨π ^ (j - 2) * A₃, by rw [h3, ← mul_assoc, ← pow_add]; congr 2; omega⟩
  have d4 : π ^ 3 ∣ W.a₄ := (pow_dvd_pow π (by omega)).trans h4
  have d6 : π ^ 4 ∣ W.a₆ :=
    ⟨π ^ (2 * j - 4) * A₆, by rw [h6, ← mul_assoc, ← pow_add]; congr 2; omega⟩
  have c3 : π ∣ W.a₃ := (dvd_pow_self π two_ne_zero).trans d3
  have c4 : π ∣ W.a₄ := (dvd_pow_self π three_ne_zero).trans d4
  have c6 : π ∣ W.a₆ := (dvd_pow_self π four_ne_zero).trans d6
  set s : Finset (Option (ResidueField 𝒪)) :=
    insert none ((quadRoots 1 (residue 𝒪 A₃) (-residue 𝒪 A₆)).image some)
  have hcard : s.card ≤ 3 := by
    have := card_quadRoots (a := (1 : ResidueField 𝒪)) (b := residue 𝒪 A₃)
      (c := -residue 𝒪 A₆) one_ne_zero
    calc s.card ≤ ((quadRoots 1 (residue 𝒪 A₃) (-residue 𝒪 A₆)).image some).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (quadRoots 1 (residue 𝒪 A₃) (-residue 𝒪 A₆)).card + 1 := by
          gcongr; exact Finset.card_image_le
      _ ≤ 3 := by omega
  refine (knBound_of_rel K W s (fun P t => ∃ (x y : 𝒪) (h : (curveK K W).Nonsingular (ι x) (ι y)),
      P = Point.some _ _ h ∧ π ∣ x ∧ π ∣ y ∧ ((¬π ^ 2 ∣ x ∧ t = none) ∨
        (π ^ 2 ∣ x ∧ ∃ Y, y = π ^ j * Y ∧ t = some (residue 𝒪 Y)))) ?_ ?_).mono K (by omega)
  · intro P hP
    obtain ⟨x, y, h, rfl, e, dx, dy⟩ := exists_of_notMem_E0Set K W hπ c3 c4 c6 hP
    by_cases hx2 : π ^ 2 ∣ x
    · obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := stageY_deep W hπ hj ⟨d1, ⟨A₂, h2, hA₂⟩,
        ⟨A₃, h3⟩, h4, ⟨A₆, h6⟩⟩ e hx2 dy
      refine ⟨some (residue 𝒪 Y), Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ?_), _, _,
        h, rfl, dx, dy, Or.inr ⟨hx2, Y, rfl, rfl⟩⟩
      apply mem_quadRoots one_ne_zero
      have := (dvd_iff_residue_eq_zero hπ).1 (stageY_quad W hπ (by omega)
        ⟨d1, ⟨A₂, h2, hA₂⟩, ⟨A₃, h3⟩, h4, ⟨A₆, h6⟩⟩ h3 h6 e)
      simp only [map_sub, map_add, map_mul, map_pow] at this
      linear_combination this
    · exact ⟨none, Finset.mem_insert_self _ _, x, y, h, rfl, dx, dy, Or.inl ⟨hx2, rfl⟩⟩
  · rintro P Q t hP hQ ⟨x, y, h, rfl, dx, dy, hPt⟩ ⟨x', y', h', rfl, dx', dy', hQt⟩
    by_contra hPQ
    obtain ⟨hn, hneg⟩ := neg_some_integral K W h'
    have hR := sub_notMem_E0Set K W hPQ
    have hQ' := neg_notMem_E0Set K W hQ
    rw [hneg] at hQ'
    have hsum : Point.some _ _ h + Point.some _ _ hn +
        (Point.some _ _ h' - Point.some _ _ h : (curveK K W).Point) = 0 := by
      rw [← hneg]; abel
    rcases hPt with ⟨hxn, rfl⟩ | ⟨hx2, Y, rfl, rfl⟩ <;>
      rcases hQt with ⟨hxn', ht⟩ | ⟨hx2', Y', rfl, ht⟩
    · obtain ⟨X₁, y₁, X₂, y₂, X₃, y₃, ⟨g₁, e₁⟩, ⟨g₂, e₂⟩, -, -, s2, s3⟩ :=
        exists_integral_coords_of_sum_zero K W hπ d1 h2 d3 d4 d6 hP hQ' hR hsum
      obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₁
      obtain ⟨hx', -⟩ := coords_eq_of_some_eq K W e₂
      subst hx'
      exact two_not_deep hπ (not_dvd_of_not_sq_dvd hπ hxn)
        (not_dvd_of_not_sq_dvd hπ hxn') s2 s3
    · exact absurd ht (by simp)
    · exact absurd ht (by simp)
    · simp only [Option.some.injEq] at ht
      have ey := equation_of_map K W h.1
      have ey' := equation_of_map K W h'.1
      obtain ⟨⟨Xd, rfl⟩, -⟩ := stageY_deep W hπ hj ⟨d1, ⟨A₂, h2, hA₂⟩, ⟨A₃, h3⟩, h4, ⟨A₆, h6⟩⟩
        ey hx2 dy
      obtain ⟨⟨Xd', rfl⟩, -⟩ := stageY_deep W hπ hj ⟨d1, ⟨A₂, h2, hA₂⟩, ⟨A₃, h3⟩, h4, ⟨A₆, h6⟩⟩
        ey' hx2' dy'
      obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, ⟨g₁, e₁⟩, ⟨g₂, e₂⟩, -, -, -, -, -, -, -, -, -, -,
        ⟨L, rfl⟩, -, l1, l2, -, -, -, -⟩ :=
        triple_cusp K W hπ d1 ⟨A₂, h2⟩ c3 c4 c6 hP hQ' hR hsum
      obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₁
      obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₂
      obtain ⟨A₁, hA₁⟩ := d1
      have hc' : π ∣ Y - Y' := by
        rw [dvd_iff_residue_eq_zero hπ, map_sub, ht, sub_self]
      apply hD _ _ Y ey hx2 rfl
      rw [hA₁, h3] at l2
      have key : π ^ j * (Y + Y' + A₃) = π ^ j * (π * (L * (Xd - Xd') - A₁ * Xd')) := by
        linear_combination l1 - l2
      have h5 : π ∣ Y + Y' + A₃ := ⟨_, mul_left_cancel₀ (pow_ne_zero j hπ.ne_zero) key⟩
      have := dvd_add h5 hc'
      convert this using 1
      ring

theorem kodairaNeron_bound_of_triple_root_x {j : ℕ} (hj : 2 ≤ j) (hS : StageX π j W) {A₂ A₄ A₆ : 𝒪}
    (h2 : W.a₂ = π * A₂) (h4 : W.a₄ = π ^ (j + 1) * A₄) (h6 : W.a₆ = π ^ (2 * j + 1) * A₆)
    (hD : ∀ x y X : 𝒪, W.toAffine.Equation x y → π ^ 2 ∣ x → π ∣ y → x = π ^ j * X →
      ¬π ∣ 2 * A₂ * X + A₄) :
    KNBound K W 4 := by
  have hS' := hS
  obtain ⟨d1, ⟨A₂', h2', hA₂⟩, h3, -, -⟩ := hS'
  have hAA : A₂' = A₂ := mul_left_cancel₀ hπ.ne_zero (h2'.symm.trans h2)
  subst hAA
  have d3 : π ^ 2 ∣ W.a₃ := (pow_dvd_pow π (by omega)).trans h3
  have d4 : π ^ 3 ∣ W.a₄ := ⟨π ^ (j - 2) * A₄, by rw [h4, ← mul_assoc, ← pow_add]; congr 2; omega⟩
  have d6 : π ^ 4 ∣ W.a₆ :=
    ⟨π ^ (2 * j - 3) * A₆, by rw [h6, ← mul_assoc, ← pow_add]; congr 2; omega⟩
  have c3 : π ∣ W.a₃ := (dvd_pow_self π two_ne_zero).trans d3
  have c4 : π ∣ W.a₄ := (dvd_pow_self π three_ne_zero).trans d4
  have c6 : π ∣ W.a₆ := (dvd_pow_self π four_ne_zero).trans d6
  have hA₂r : residue 𝒪 A₂' ≠ 0 := fun h0 => hA₂ ((dvd_iff_residue_eq_zero hπ).2 h0)
  set s : Finset (Option (ResidueField 𝒪)) :=
    insert none ((quadRoots (residue 𝒪 A₂') (residue 𝒪 A₄) (residue 𝒪 A₆)).image some)
  have hcard : s.card ≤ 3 := by
    have := card_quadRoots (a := residue 𝒪 A₂') (b := residue 𝒪 A₄) (c := residue 𝒪 A₆) hA₂r
    calc s.card ≤ ((quadRoots (residue 𝒪 A₂') (residue 𝒪 A₄) (residue 𝒪 A₆)).image some).card
            + 1 := Finset.card_insert_le _ _
      _ ≤ (quadRoots (residue 𝒪 A₂') (residue 𝒪 A₄) (residue 𝒪 A₆)).card + 1 := by
          gcongr; exact Finset.card_image_le
      _ ≤ 3 := by omega
  refine (knBound_of_rel K W s (fun P t => ∃ (x y : 𝒪) (h : (curveK K W).Nonsingular (ι x) (ι y)),
      P = Point.some _ _ h ∧ π ∣ x ∧ π ∣ y ∧ ((¬π ^ 2 ∣ x ∧ t = none) ∨
        (π ^ 2 ∣ x ∧ ∃ X, x = π ^ j * X ∧ t = some (residue 𝒪 X)))) ?_ ?_).mono K (by omega)
  · intro P hP
    obtain ⟨x, y, h, rfl, e, dx, dy⟩ := exists_of_notMem_E0Set K W hπ c3 c4 c6 hP
    by_cases hx2 : π ^ 2 ∣ x
    · obtain ⟨⟨X, rfl⟩, ⟨Y, rfl⟩⟩ := stageX_deep W hπ hj hS e hx2 dy
      refine ⟨some (residue 𝒪 X), Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ?_), _, _,
        h, rfl, dx, dy, Or.inr ⟨hx2, X, rfl, rfl⟩⟩
      apply mem_quadRoots hA₂r
      have := (dvd_iff_residue_eq_zero hπ).1 (stageX_quad W hπ hj hS h2 h4 h6 e)
      simp only [map_add, map_mul, map_pow] at this
      linear_combination this
    · exact ⟨none, Finset.mem_insert_self _ _, x, y, h, rfl, dx, dy, Or.inl ⟨hx2, rfl⟩⟩
  · rintro P Q t hP hQ ⟨x, y, h, rfl, dx, dy, hPt⟩ ⟨x', y', h', rfl, dx', dy', hQt⟩
    by_contra hPQ
    obtain ⟨hn, hneg⟩ := neg_some_integral K W h'
    have hR := sub_notMem_E0Set K W hPQ
    have hQ' := neg_notMem_E0Set K W hQ
    rw [hneg] at hQ'
    have hsum : Point.some _ _ h + Point.some _ _ hn +
        (Point.some _ _ h' - Point.some _ _ h : (curveK K W).Point) = 0 := by
      rw [← hneg]; abel
    rcases hPt with ⟨hxn, rfl⟩ | ⟨hx2, X, rfl, rfl⟩ <;>
      rcases hQt with ⟨hxn', ht⟩ | ⟨hx2', X', rfl, ht⟩
    · obtain ⟨X₁, y₁, X₂, y₂, X₃, y₃, ⟨g₁, e₁⟩, ⟨g₂, e₂⟩, -, -, s2, s3⟩ :=
        exists_integral_coords_of_sum_zero K W hπ d1 h2 d3 d4 d6 hP hQ' hR hsum
      obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₁
      obtain ⟨hx', -⟩ := coords_eq_of_some_eq K W e₂
      subst hx'
      exact two_not_deep hπ (not_dvd_of_not_sq_dvd hπ hxn)
        (not_dvd_of_not_sq_dvd hπ hxn') s2 s3
    · exact absurd ht (by simp)
    · exact absurd ht (by simp)
    · simp only [Option.some.injEq] at ht
      have ey := equation_of_map K W h.1
      obtain ⟨-, ⟨Y, rfl⟩⟩ := stageX_deep W hπ hj hS ey hx2 dy
      obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, ⟨g₁, e₁⟩, ⟨g₂, e₂⟩, -, -, -, -, -, -, -, -,
        ⟨X₃, rfl⟩, -, ⟨L, rfl⟩, -, l1, -, -, v1, v2, -⟩ :=
        triple_cusp K W hπ d1 ⟨A₂', h2⟩ c3 c4 c6 hP hQ' hR hsum
      obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₁
      obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₂
      obtain ⟨A₁, hA₁⟩ := d1
      obtain ⟨B₃, hB₃⟩ := h3
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
      have hν : ν = π ^ (i + 3) * (Y - L * X) := by linear_combination -l1
      subst hν
      rw [hA₁, h2] at v1
      rw [hA₁, hB₃, h4] at v2
      have hπ0 := hπ.ne_zero
      have s1 : π ∣ X₃ + A₂' := ⟨L ^ 2 + A₁ * L - π ^ i * (X + X'),
        mul_left_cancel₀ hπ0 (by linear_combination v1)⟩
      have s2 : π ∣ X₃ * (X + X') - A₄ :=
        ⟨-π ^ i * X * X' - 2 * L * (Y - L * X) - A₁ * (Y - L * X) - B₃ * L,
          mul_left_cancel₀ (pow_ne_zero (i + 3) hπ0) (by linear_combination v2)⟩
      have s0 : π ∣ X - X' := by
        rw [dvd_iff_residue_eq_zero hπ, map_sub, ht, sub_self]
      apply hD _ _ X ey hx2 dy rfl
      have := dvd_sub (dvd_add (dvd_mul_of_dvd_right s0 A₂') (dvd_mul_of_dvd_left s1 (X + X'))) s2
      convert this using 1
      ring

omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] hπ in
theorem vc_Δ_one (r s t : 𝒪) : ((⟨1, r, s, t⟩ : VariableChange 𝒪) • W).Δ = W.Δ := by
  simp [variableChange_Δ]

omit [IsFractionRing 𝒪 K] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] in

theorem exists_not_pow_dvd {a : 𝒪} (ha : a ≠ 0) : ∃ n, ¬π ^ n ∣ a := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n + 1, fun ⟨c, hc⟩ => hπ.not_isUnit ?_⟩
  have : (u : 𝒪) = π * c := by
    apply mul_right_cancel₀ (pow_ne_zero n hπ.ne_zero)
    rw [hc]; ring
  exact isUnit_of_dvd_unit ⟨c, this⟩ u.isUnit

theorem kodairaNeron_bound_of_Istar_induction (N : ℕ) : ∀ (d j : ℕ) (W' : WeierstrassCurve 𝒪)
    [(W'.map (algebraMap 𝒪 K)).IsElliptic], 2 ≤ j → j + d = N → ¬π ^ N ∣ W'.Δ →
      StageY π j W' → KNBound K W' 4 := by
  intro d
  induction d with
  | zero =>
    intro j W' _ hj hjd hN hS
    exfalso
    apply hN
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    exact (pow_dvd_pow π (by omega)).trans (stageY_dvd_Δ W' hπ hS)
  | succ d ih =>
    intro j W' _ hj hjd hN hS
    obtain ⟨d1, ⟨A₂, h2, hA₂⟩, ⟨A₃, h3⟩, h4, ⟨A₆, h6⟩⟩ := id hS
    by_cases hex : ∃ x y Y : 𝒪, W'.toAffine.Equation x y ∧ π ^ 2 ∣ x ∧ y = π ^ j * Y ∧
        π ∣ 2 * Y + A₃
    · obtain ⟨x, y, Y, e, hx2, rfl, hD⟩ := hex
      obtain ⟨⟨X, rfl⟩, -⟩ := stageY_deep W' hπ hj hS e hx2
        (dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) Y)
      have hQ := stageY_quad W' hπ (by omega) hS h3 h6 e
      have hS₁ := vc_stageY_step W' hπ hS h3 h6 hQ hD
      refine KNBound.of_vc K W' ⟨1, 0, 0, π ^ j * Y⟩ ?_
      obtain ⟨-, ⟨B₂, g2, -⟩, -, ⟨B₄, g4⟩, ⟨B₆, g6⟩⟩ := id hS₁
      by_cases hex' : ∃ x y X : 𝒪,
          (((⟨1, 0, 0, π ^ j * Y⟩ : VariableChange 𝒪) • W').toAffine.Equation x y) ∧
          π ^ 2 ∣ x ∧ π ∣ y ∧ x = π ^ j * X ∧ π ∣ 2 * B₂ * X + B₄
      · obtain ⟨x₁, y₁, X₁, e', hx2', dy', rfl, hD'⟩ := hex'
        obtain ⟨-, ⟨Y₁, rfl⟩⟩ := stageX_deep _ hπ hj hS₁ e' hx2' dy'
        have hQ' := stageX_quad _ hπ hj hS₁ g2 g4 g6 e'
        have hS₂ := vc_stageX_step _ hπ hj hS₁ g2 g4 g6 hQ' hD'
        refine KNBound.of_vc K _ ⟨1, π ^ j * X₁, 0, 0⟩ ?_
        exact ih (j + 1) _ (by omega) (by omega) (by rwa [vc_Δ_one, vc_Δ_one]) hS₂
      · push Not at hex'
        exact kodairaNeron_bound_of_triple_root_x K _ hπ hj hS₁ g2 g4 g6
          fun x y X e hx hy hX hD => hex' x y X e hx hy hX hD
    · push Not at hex
      exact kodairaNeron_bound_of_double_root_y K W' hπ hj hS h3 h6 fun x y Y e hx hy hD => hex x y Y e hx hy hD

theorem knBound_Istar (hΔ : W.Δ ≠ 0) (hS : StageY π 2 W) : KNBound K W 4 := by
  obtain ⟨n, hn⟩ := exists_not_pow_dvd hπ hΔ
  exact kodairaNeron_bound_of_Istar_induction K hπ (n + 2) n 2 W le_rfl (by omega)
    (fun h => hn ((pow_dvd_pow π (by omega)).trans h)) hS

end Bound

end

end GroundTheory.Arith.Abelian
