import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial

noncomputable section

section Roots

variable {k : Type*} [Field k] [DecidableEq k]

def quadRoots (a b c : k) : Finset k := (C a * X ^ 2 + C b * X + C c).roots.toFinset

theorem card_quadRoots {a b c : k} (ha : a ≠ 0) : (quadRoots a b c).card ≤ 2 :=
  calc (quadRoots a b c).card ≤ Multiset.card (C a * X ^ 2 + C b * X + C c).roots := by
        unfold quadRoots; exact Multiset.toFinset_card_le _
    _ ≤ _ := card_roots' _
    _ = 2 := natDegree_quadratic ha

theorem mem_quadRoots {a b c t : k} (ha : a ≠ 0) (h : a * t ^ 2 + b * t + c = 0) :
    t ∈ quadRoots a b c := by
  unfold quadRoots
  rw [Multiset.mem_toFinset, mem_roots']
  refine ⟨fun h0 => ?_, by simp [h]⟩
  have := congrArg natDegree h0
  rw [natDegree_quadratic ha, natDegree_zero] at this
  exact absurd this (by norm_num)

def cubicRoots (a b c d : k) : Finset k := (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d).roots.toFinset

theorem card_cubicRoots {a b c d : k} (ha : a ≠ 0) : (cubicRoots a b c d).card ≤ 3 :=
  calc (cubicRoots a b c d).card ≤
        Multiset.card (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d).roots := by
        unfold cubicRoots; exact Multiset.toFinset_card_le _
    _ ≤ _ := card_roots' _
    _ = 3 := natDegree_cubic ha

theorem mem_cubicRoots {a b c d t : k} (ha : a ≠ 0) (h : a * t ^ 3 + b * t ^ 2 + c * t + d = 0) :
    t ∈ cubicRoots a b c d := by
  unfold cubicRoots
  rw [Multiset.mem_toFinset, mem_roots']
  refine ⟨fun h0 => ?_, by simp [h]⟩
  have := congrArg natDegree h0
  rw [natDegree_cubic ha, natDegree_zero] at this
  exact absurd this (by norm_num)

end Roots

section Algebra

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] (W : WeierstrassCurve 𝒪) {π : 𝒪}
  (hπ : Irreducible π)
include hπ

theorem dvd_quad_IV (h1 : π ∣ W.a₁) (h2 : π ∣ W.a₂) {A₃ A₆ : 𝒪} (h3 : W.a₃ = π * A₃)
    (h4 : π ^ 2 ∣ W.a₄) (h6 : W.a₆ = π ^ 2 * A₆) {x y Y : 𝒪} (e : W.toAffine.Equation x y)
    (dx : π ∣ x) (hy : y = π * Y) : π ∣ Y ^ 2 + A₃ * Y - A₆ := by
  obtain ⟨A₁, hA₁⟩ := h1
  obtain ⟨A₂, hA₂⟩ := h2
  obtain ⟨A₄, hA₄⟩ := h4
  obtain ⟨X, rfl⟩ := dx
  subst hy
  rw [equation_iff, hA₁, hA₂, h3, hA₄, h6] at e
  have hπ0 : π ^ 2 ≠ 0 := pow_ne_zero _ hπ.ne_zero
  refine ⟨X ^ 3 + A₂ * X ^ 2 + A₄ * X - A₁ * X * Y, mul_left_cancel₀ hπ0 ?_⟩
  linear_combination e

theorem vc_IV_step (h1 : π ∣ W.a₁) (h2 : π ∣ W.a₂) {A₃ A₆ : 𝒪} (h3 : W.a₃ = π * A₃)
    (h4 : π ^ 2 ∣ W.a₄) (h6 : W.a₆ = π ^ 2 * A₆) {x₁ y₁ Y₁ : 𝒪} (e : W.toAffine.Equation x₁ y₁)
    (dx : π ∣ x₁) (hy : y₁ = π * Y₁) (hD : π ∣ 2 * Y₁ + A₃) :
    let W' := (⟨1, 0, 0, y₁⟩ : VariableChange 𝒪) • W
    π ∣ W'.a₁ ∧ π ∣ W'.a₂ ∧ π ^ 2 ∣ W'.a₃ ∧ π ^ 2 ∣ W'.a₄ ∧ π ^ 3 ∣ W'.a₆ := by
  have hQ := dvd_quad_IV W hπ h1 h2 h3 h4 h6 e dx hy
  intro W'
  simp only [W', variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul]
  obtain ⟨A₁, hA₁⟩ := h1
  obtain ⟨A₂, hA₂⟩ := h2
  obtain ⟨A₄, hA₄⟩ := h4
  obtain ⟨Z, hZ⟩ := hD
  obtain ⟨Z', hZ'⟩ := hQ
  subst hy
  refine ⟨⟨A₁, by rw [hA₁]; ring⟩, ⟨A₂ - 0 * A₁, by rw [hA₂, hA₁]; ring⟩, ⟨Z, ?_⟩,
    ⟨A₄ - Y₁ * A₁, ?_⟩, ⟨-Z', ?_⟩⟩
  · rw [h3]; linear_combination π * hZ
  · rw [hA₄, hA₁]; ring
  · rw [h6, h3]; linear_combination (-π ^ 2) * hZ'

end Algebra

section Bound

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [DecidableEq K]
  [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

def KNBound (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic] (n : ℕ) : Prop :=
  Finite ((curveK K W).Point ⧸ E0 K W) ∧ Nat.card ((curveK K W).Point ⧸ E0 K W) ≤ n

variable (W : WeierstrassCurve 𝒪) [(W.map (algebraMap 𝒪 K)).IsElliptic]

local notation "ι" => algebraMap 𝒪 K

theorem KNBound.mono {W : WeierstrassCurve 𝒪} [(W.map (algebraMap 𝒪 K)).IsElliptic] {n m : ℕ}
    (h : KNBound K W n) (hnm : n ≤ m) : KNBound K W m :=
  ⟨h.1, h.2.trans hnm⟩

theorem KNBound.of_vc (C : VariableChange 𝒪) {n : ℕ} (h : KNBound K (C • W) n) :
    KNBound K W n := by
  have e := (quotientE0VariableChangeEquiv K W C).toEquiv
  haveI := h.1
  exact ⟨Finite.of_equiv _ e.symm, by rw [Nat.card_congr e]; exact h.2⟩

theorem knBound_of_rel {T : Type*} (s : Finset T) (R : (curveK K W).Point → T → Prop)
    (hex : ∀ P, P ∉ E0Set K W → ∃ t ∈ s, R P t)
    (hinj : ∀ P Q t, P ∉ E0Set K W → Q ∉ E0Set K W → R P t → R Q t → P - Q ∈ E0Set K W) :
    KNBound K W (s.card + 1) :=
  card_quotient_le_of_rel (E0 K W) s R hex hinj

theorem knBound_two (hno : ∀ P Q R, P ∉ E0Set K W → Q ∉ E0Set K W → R ∉ E0Set K W →
    P + Q + R ≠ 0) : KNBound K W 2 :=
  card_quotient_le_two (E0 K W) hno

theorem knBound_one (hall : ∀ P, P ∈ E0Set K W) : KNBound K W 1 := by
  have := knBound_of_rel K W (∅ : Finset Unit) (fun _ _ => True)
    (fun P hP => absurd (hall P) hP) (fun P _ _ hP => absurd (hall P) hP)
  simpa using this

theorem neg_notMem_E0Set {P : (curveK K W).Point} (hP : P ∉ E0Set K W) : -P ∉ E0Set K W :=
  fun h => hP (by simpa using (E0 K W).neg_mem (show -P ∈ E0 K W from h) : P ∈ E0 K W)

theorem sub_notMem_E0Set {P Q : (curveK K W).Point} (h : P - Q ∉ E0Set K W) :
    Q - P ∉ E0Set K W :=
  fun h' => h (by simpa using (E0 K W).neg_mem (show Q - P ∈ E0 K W from h') : P - Q ∈ E0 K W)

variable {π : 𝒪} (hπ : Irreducible π)
include hπ

theorem triple_cusp (h1 : π ∣ W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄)
    (h6 : π ∣ W.a₆) {P₁ P₂ P₃ : (curveK K W).Point} (hP₁ : P₁ ∉ E0Set K W)
    (hP₂ : P₂ ∉ E0Set K W) (hP₃ : P₃ ∉ E0Set K W) (hs : P₁ + P₂ + P₃ = 0) :
    ∃ x₁ y₁ x₂ y₂ x₃ y₃ ℓ ν : 𝒪,
      (∃ h, P₁ = Point.some (ι x₁) (ι y₁) h) ∧ (∃ h, P₂ = Point.some (ι x₂) (ι y₂) h) ∧
      (∃ h, P₃ = Point.some (ι x₃) (ι y₃) h) ∧
      W.toAffine.Equation x₁ y₁ ∧ W.toAffine.Equation x₂ y₂ ∧ W.toAffine.Equation x₃ y₃ ∧
      π ∣ x₁ ∧ π ∣ y₁ ∧ π ∣ x₂ ∧ π ∣ y₂ ∧ π ∣ x₃ ∧ π ∣ y₃ ∧ π ∣ ℓ ∧ π ∣ ν ∧
      y₁ = ℓ * x₁ + ν ∧ y₂ = ℓ * x₂ + ν ∧ y₃ = ℓ * x₃ + ν ∧
      x₁ + x₂ + x₃ = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * ℓ * ν - W.a₁ * ν - W.a₃ * ℓ ∧
      x₁ * x₂ * x₃ = ν ^ 2 + W.a₃ * ν - W.a₆ := by
  obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, p₁, p₂, p₃, e₁, e₂, e₃, dx₁, dy₁, dx₂, dy₂, dx₃, dy₃,
    l1, l2, l3, v1, v2, v3⟩ := triple_origin K W hπ h3 h4 h6 hP₁ hP₂ hP₃ hs
  have hℓ : π ∣ ℓ := by
    apply hπ.prime.dvd_of_dvd_pow (n := 2)
    have : ℓ ^ 2 = (x₁ + x₂ + x₃) - W.a₁ * ℓ + W.a₂ := by linear_combination -v1
    rw [this]
    exact dvd_add (dvd_sub (dvd_add (dvd_add dx₁ dx₂) dx₃) (h1.mul_right _)) h2
  have hν : π ∣ ν := by
    have : ν = y₁ - ℓ * x₁ := by linear_combination -l1
    rw [this]
    exact dvd_sub dy₁ (hℓ.mul_right _)
  exact ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, p₁, p₂, p₃, e₁, e₂, e₃, dx₁, dy₁, dx₂, dy₂, dx₃, dy₃,
    hℓ, hν, l1, l2, l3, v1, v2, v3⟩

theorem knBound_III (h1 : π ∣ W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ W.a₃) (h4 : π ∣ W.a₄)
    (h6 : π ∣ W.a₆) (h4' : ¬π ^ 2 ∣ W.a₄) : KNBound K W 2 := by
  refine knBound_two K W fun P Q R hP hQ hR hs => ?_
  obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, -, -, -, -, -, -, ⟨X₁, rfl⟩, -, ⟨X₂, rfl⟩, -, ⟨X₃, rfl⟩, -,
    ⟨L, rfl⟩, ⟨V, rfl⟩, -, -, -, -, v2, -⟩ := triple_cusp K W hπ h1 h2 h3 h4 h6 hP hQ hR hs
  obtain ⟨A₁, hA₁⟩ := h1
  obtain ⟨A₃, hA₃⟩ := h3
  apply h4'
  refine ⟨X₁ * X₂ + X₁ * X₃ + X₂ * X₃ + 2 * L * V + A₁ * V + A₃ * L, ?_⟩
  rw [hA₁, hA₃] at v2
  linear_combination -v2

theorem knBound_IV (h1 : π ∣ W.a₁) (h2 : π ∣ W.a₂) {A₃ A₆ : 𝒪} (h3 : W.a₃ = π * A₃)
    (h4 : π ^ 2 ∣ W.a₄) (h6 : W.a₆ = π ^ 2 * A₆)
    (hD : ∀ x y Y : 𝒪, W.toAffine.Equation x y → π ∣ x → y = π * Y → ¬π ∣ 2 * Y + A₃) :
    KNBound K W 3 := by
  have h3' : π ∣ W.a₃ := ⟨A₃, h3⟩
  have h4' : π ∣ W.a₄ := (dvd_pow_self π two_ne_zero).trans h4
  have h6' : π ∣ W.a₆ := ⟨π * A₆, by rw [h6]; ring⟩
  have hcard := card_quadRoots (a := (1 : ResidueField 𝒪)) (b := residue 𝒪 A₃)
    (c := -residue 𝒪 A₆) one_ne_zero
  refine (knBound_of_rel K W (quadRoots 1 (residue 𝒪 A₃) (-residue 𝒪 A₆))
    (fun P c => ∃ (x y Y : 𝒪) (h : (curveK K W).Nonsingular (ι x) (ι y)),
      P = Point.some _ _ h ∧ π ∣ x ∧ y = π * Y ∧ residue 𝒪 Y = c) ?_ ?_).mono K (by omega)
  · intro P hP
    obtain ⟨x, y, h, rfl, e, dx, Y, rfl⟩ := exists_of_notMem_E0Set K W hπ h3' h4' h6' hP
    refine ⟨residue 𝒪 Y, mem_quadRoots one_ne_zero ?_, x, π * Y, Y, h, rfl, dx, rfl, rfl⟩
    have := (dvd_iff_residue_eq_zero hπ).1 (dvd_quad_IV W hπ h1 h2 h3 h4 h6 e dx rfl)
    simp only [map_sub, map_add, map_mul, map_pow] at this
    linear_combination this
  · rintro P Q c hP hQ ⟨x, y, Y, h, rfl, dx, rfl, rfl⟩ ⟨x', y', Y', h', rfl, dx', rfl, hc⟩
    by_contra hPQ
    obtain ⟨hn, hneg⟩ := neg_some_integral K W h'
    have hR := sub_notMem_E0Set K W hPQ
    have hQ' := neg_notMem_E0Set K W hQ
    rw [hneg] at hQ'
    obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, ℓ, ν, ⟨g₁, e₁⟩, ⟨g₂, e₂⟩, -, -, -, -, -, -, -, -, -, -,
      ⟨L, rfl⟩, -, l1, l2, -, -, -, -⟩ := triple_cusp K W hπ h1 h2 h3' h4' h6' hP hQ' hR
        (by rw [← hneg]; abel)
    obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₁
    obtain ⟨rfl, rfl⟩ := coords_eq_of_some_eq K W e₂
    obtain ⟨A₁, hA₁⟩ := h1
    obtain ⟨X, rfl⟩ := dx
    obtain ⟨X', rfl⟩ := dx'
    have hc' : π ∣ Y - Y' := by
      rw [dvd_iff_residue_eq_zero hπ, map_sub, hc, sub_self]
    apply hD (π * X) (π * Y) Y (equation_of_map K W h.1) (dvd_mul_right π X) rfl
    rw [hA₁, h3] at l2
    have key : π * (Y + Y' + A₃) = π * (π * (L * (X - X') - A₁ * X')) := by
      linear_combination l1 - l2
    have h5 : π ∣ Y + Y' + A₃ := ⟨_, mul_left_cancel₀ hπ.ne_zero key⟩
    have := dvd_add h5 hc'
    convert this using 1
    ring

end Bound

end

end GroundTheory.Arith.Abelian
