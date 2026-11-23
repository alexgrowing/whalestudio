import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeronReduction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

noncomputable section

open IsDiscreteValuationRing

def iotaN (n : ℕ) (a b : ℕ∞) : ZMod n :=
  if b ≤ a then ((b.toNat : ℕ) : ZMod n) else -((a.toNat : ℕ) : ZMod n)

theorem top_ne_three_mul (τ : ℕ) : (⊤ : ℕ∞) ≠ 3 * (τ : ℕ∞) := by
  have : (3 : ℕ∞) * (τ : ℕ∞) = ((3 * τ : ℕ) : ℕ∞) := by push_cast; rfl
  rw [this]; exact (ENat.natCast_ne_top _).symm

theorem top_ne_two_mul (τ : ℕ) : (⊤ : ℕ∞) ≠ 2 * (τ : ℕ∞) := by
  have : (2 : ℕ∞) * (τ : ℕ∞) = ((2 * τ : ℕ) : ℕ∞) := by push_cast; rfl
  rw [this]; exact (ENat.natCast_ne_top _).symm

theorem iotaN_of_le {n : ℕ} {a b : ℕ∞} (h : b ≤ a) : iotaN n a b = ((b.toNat : ℕ) : ZMod n) := by
  simp [iotaN, h]

theorem iotaN_of_lt {n : ℕ} {a b : ℕ∞} (h : a < b) : iotaN n a b = -((a.toNat : ℕ) : ZMod n) := by
  simp [iotaN, not_le.2 h]

theorem iotaN_swap {n : ℕ} {a b : ℕ∞} (htie : a = b → 2 * a = n) :
    iotaN n b a = -iotaN n a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [iotaN_of_le h.le, iotaN_of_lt h, neg_neg]
  · subst h
    rw [iotaN_of_le le_rfl, eq_neg_iff_add_eq_zero]
    have h2 := htie rfl
    have ha : a ≠ ⊤ := by rintro rfl; simp at h2
    lift a to ℕ using ha
    simp only [ENat.toNat_natCast]
    rw [← Nat.cast_add, ← two_mul]
    have : 2 * a = n := by exact_mod_cast h2
    rw [this, ZMod.natCast_self]
  · rw [iotaN_of_lt h, iotaN_of_le h.le]

theorem iotaN_two {n : ℕ} {τ aP bP aR bR : ℕ∞} (hτ : 1 ≤ τ)
    (cP : (aP = bP ∧ 2 * aP = n) ∨ (aP ≠ bP ∧ min aP bP = τ))
    (cR : (aR = bR ∧ 2 * aR = n) ∨ (aR ≠ bR ∧ min aR bR = τ))
    (sP : aP ≠ bP → (3 * τ < n → aP + bP = 3 * τ) ∧ (n < 3 * τ → aP + bP = n))
    (sR : aR ≠ bR → (3 * τ < n → aR + bR = 3 * τ) ∧ (n < 3 * τ → aR + bR = n))
    (hα : (3 * τ < n → aP + aR = 3 * τ) ∧ (n < 3 * τ → aP + aR = n) ∧ (3 * τ = n → n ≤ aP + aR))
    (hβ : (3 * τ < n → bP + bR = 3 * τ) ∧ (n < 3 * τ → bP + bR = n) ∧ (3 * τ = n → n ≤ bP + bR)) :
    iotaN n aP bP + iotaN n aR bR = 0 := by
  have fin_of_two : ∀ {a : ℕ∞}, 2 * a = (n : ℕ∞) → a ≠ ⊤ := by
    intro a h; rintro rfl; simp at h
  have min_cases : ∀ {a b : ℕ∞}, a ≠ b → min a b = τ → (a = τ ∧ τ < b) ∨ (b = τ ∧ τ < a) := by
    intro a b hab hm
    rcases le_total a b with h | h
    · rw [min_eq_left h] at hm; exact Or.inl ⟨hm, hm ▸ lt_of_le_of_ne h hab⟩
    · rw [min_eq_right h] at hm; exact Or.inr ⟨hm, hm ▸ lt_of_le_of_ne h (Ne.symm hab)⟩
  have hτ' : ∀ {a b : ℕ∞}, a ≠ b → min a b = τ → τ ≠ ⊤ := by
    intro a b hab hm hτt
    rw [hτt, min_eq_top] at hm
    exact hab (hm.1.trans hm.2.symm)
  rcases cP with ⟨tP, hP⟩ | ⟨nP, mP⟩ <;> rcases cR with ⟨tR, hR⟩ | ⟨nR, mR⟩
  · subst tP tR
    rw [iotaN_of_le le_rfl, iotaN_of_le le_rfl]
    lift aP to ℕ using fin_of_two hP
    lift aR to ℕ using fin_of_two hR
    simp only [ENat.toNat_natCast]
    have h1 : 2 * aP = n := by exact_mod_cast hP
    have h2 : 2 * aR = n := by exact_mod_cast hR
    rw [← Nat.cast_add, show aP + aR = n by omega, ZMod.natCast_self]
  · exfalso
    subst tP
    have hτf := hτ' nR mR
    lift τ to ℕ using hτf
    lift aP to ℕ using fin_of_two hP
    have h1 : 2 * aP = n := by exact_mod_cast hP
    have hτ1 : 1 ≤ τ := by exact_mod_cast hτ
    rcases lt_trichotomy (3 * τ) n with h | h | h
    · have e1 := hα.1 (by exact_mod_cast h)
      have e2 := hβ.1 (by exact_mod_cast h)
      have haR : aR ≠ ⊤ := by rintro rfl; simp at e1; exact absurd e1 (top_ne_three_mul τ)
      have hbR : bR ≠ ⊤ := by rintro rfl; simp at e2; exact absurd e2 (top_ne_three_mul τ)
      lift aR to ℕ using haR
      lift bR to ℕ using hbR
      apply nR
      have e1' : aP + aR = 3 * τ := by exact_mod_cast e1
      have e2' : aP + bR = 3 * τ := by exact_mod_cast e2
      exact_mod_cast (show aR = bR by omega)
    · have e1 := hα.2.2 (by exact_mod_cast h)
      have e2 := hβ.2.2 (by exact_mod_cast h)
      rcases min_cases nR mR with ⟨hm, -⟩ | ⟨hm, -⟩
      · rw [hm] at e1
        have : n ≤ aP + τ := by exact_mod_cast e1
        omega
      · rw [hm] at e2
        have : n ≤ aP + τ := by exact_mod_cast e2
        omega
    · have e1 := hα.2.1 (by exact_mod_cast h)
      have e2 := hβ.2.1 (by exact_mod_cast h)
      have haR : aR ≠ ⊤ := by rintro rfl; simp at e1
      have hbR : bR ≠ ⊤ := by rintro rfl; simp at e2
      lift aR to ℕ using haR
      lift bR to ℕ using hbR
      apply nR
      have e1' : aP + aR = n := by exact_mod_cast e1
      have e2' : aP + bR = n := by exact_mod_cast e2
      exact_mod_cast (show aR = bR by omega)
  · exfalso
    subst tR
    have hτf := hτ' nP mP
    lift τ to ℕ using hτf
    lift aR to ℕ using fin_of_two hR
    have h1 : 2 * aR = n := by exact_mod_cast hR
    have hτ1 : 1 ≤ τ := by exact_mod_cast hτ
    rcases lt_trichotomy (3 * τ) n with h | h | h
    · have e1 := hα.1 (by exact_mod_cast h)
      have e2 := hβ.1 (by exact_mod_cast h)
      have haP : aP ≠ ⊤ := by rintro rfl; simp at e1; exact absurd e1 (top_ne_three_mul τ)
      have hbP : bP ≠ ⊤ := by rintro rfl; simp at e2; exact absurd e2 (top_ne_three_mul τ)
      lift aP to ℕ using haP
      lift bP to ℕ using hbP
      apply nP
      have e1' : aP + aR = 3 * τ := by exact_mod_cast e1
      have e2' : bP + aR = 3 * τ := by exact_mod_cast e2
      exact_mod_cast (show aP = bP by omega)
    · have e1 := hα.2.2 (by exact_mod_cast h)
      have e2 := hβ.2.2 (by exact_mod_cast h)
      rcases min_cases nP mP with ⟨hm, -⟩ | ⟨hm, -⟩
      · rw [hm] at e1
        have : n ≤ τ + aR := by exact_mod_cast e1
        omega
      · rw [hm] at e2
        have : n ≤ τ + aR := by exact_mod_cast e2
        omega
    · have e1 := hα.2.1 (by exact_mod_cast h)
      have e2 := hβ.2.1 (by exact_mod_cast h)
      have haP : aP ≠ ⊤ := by rintro rfl; simp at e1
      have hbP : bP ≠ ⊤ := by rintro rfl; simp at e2
      lift aP to ℕ using haP
      lift bP to ℕ using hbP
      apply nP
      have e1' : aP + aR = n := by exact_mod_cast e1
      have e2' : bP + aR = n := by exact_mod_cast e2
      exact_mod_cast (show aP = bP by omega)
  · have hτf := hτ' nP mP
    lift τ to ℕ using hτf
    have hτ1 : 1 ≤ τ := by exact_mod_cast hτ
    rcases lt_trichotomy (3 * τ) n with h | h | h
    · have e1 := hα.1 (by exact_mod_cast h)
      have e2 := hβ.1 (by exact_mod_cast h)
      have e3 := (sP nP).1 (by exact_mod_cast h)
      have e4 := (sR nR).1 (by exact_mod_cast h)
      have haP : aP ≠ ⊤ := by rintro rfl; simp at e1; exact absurd e1 (top_ne_three_mul τ)
      have hbP : bP ≠ ⊤ := by rintro rfl; simp at e2; exact absurd e2 (top_ne_three_mul τ)
      have haR : aR ≠ ⊤ := by rintro rfl; simp at e1; exact absurd e1 (top_ne_three_mul τ)
      have hbR : bR ≠ ⊤ := by rintro rfl; simp at e2; exact absurd e2 (top_ne_three_mul τ)
      lift aP to ℕ using haP
      lift bP to ℕ using hbP
      lift aR to ℕ using haR
      lift bR to ℕ using hbR
      have e1' : aP + aR = 3 * τ := by exact_mod_cast e1
      have e3' : aP + bP = 3 * τ := by exact_mod_cast e3
      have e4' : aR + bR = 3 * τ := by exact_mod_cast e4
      rw [show aR = bP by omega, show bR = aP by omega,
        iotaN_swap (fun h => absurd h nP), add_neg_cancel]
    · rcases min_cases nP mP with ⟨hmP, hlP⟩ | ⟨hmP, hlP⟩ <;>
        rcases min_cases nR mR with ⟨hmR, hlR⟩ | ⟨hmR, hlR⟩
      · have e1 := hα.2.2 (by exact_mod_cast h)
        rw [hmP, hmR] at e1
        have : n ≤ τ + τ := by exact_mod_cast e1
        omega
      · rw [iotaN_of_lt (hmP ▸ hlP), iotaN_of_le (hmR ▸ hlR).le, hmP, hmR, neg_add_cancel]
      · rw [iotaN_of_le (hmP ▸ hlP).le, iotaN_of_lt (hmR ▸ hlR), hmP, hmR, add_neg_cancel]
      · have e2 := hβ.2.2 (by exact_mod_cast h)
        rw [hmP, hmR] at e2
        have : n ≤ τ + τ := by exact_mod_cast e2
        omega
    · have e1 := hα.2.1 (by exact_mod_cast h)
      have e2 := hβ.2.1 (by exact_mod_cast h)
      have e3 := (sP nP).2 (by exact_mod_cast h)
      have e4 := (sR nR).2 (by exact_mod_cast h)
      have haP : aP ≠ ⊤ := by rintro rfl; simp at e1
      have hbP : bP ≠ ⊤ := by rintro rfl; simp at e2
      have haR : aR ≠ ⊤ := by rintro rfl; simp at e1
      have hbR : bR ≠ ⊤ := by rintro rfl; simp at e2
      lift aP to ℕ using haP
      lift bP to ℕ using hbP
      lift aR to ℕ using haR
      lift bR to ℕ using hbR
      have e1' : aP + aR = n := by exact_mod_cast e1
      have e3' : aP + bP = n := by exact_mod_cast e3
      have e4' : aR + bR = n := by exact_mod_cast e4
      rw [show aR = bP by omega, show bR = aP by omega,
        iotaN_swap (fun h => absurd h nP), add_neg_cancel]

theorem iotaN_three {n : ℕ} {N a₁ b₁ m₁ a₂ b₂ m₂ a₃ b₃ m₃ : ℕ∞} (hN : 1 ≤ N)
    (c₁ : (a₁ < b₁ ∧ a₁ = N ∧ m₁ = N) ∨ (b₁ ≤ a₁ ∧ b₁ = min m₁ N))
    (c₂ : (a₂ < b₂ ∧ a₂ = N ∧ m₂ = N) ∨ (b₂ ≤ a₂ ∧ b₂ = min m₂ N))
    (c₃ : (a₃ < b₃ ∧ a₃ = N ∧ m₃ = N) ∨ (b₃ ≤ a₃ ∧ b₃ = min m₃ N))
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hm₃ : 1 ≤ m₃)
    (s₁ : a₁ < b₁ → (n : ℕ∞) < 3 * N → a₁ + b₁ = n)
    (s₂ : a₂ < b₂ → (n : ℕ∞) < 3 * N → a₂ + b₂ = n)
    (s₃ : a₃ < b₃ → (n : ℕ∞) < 3 * N → a₃ + b₃ = n)
    (hsm : 2 * N < n → m₁ + m₂ + m₃ = 2 * N)
    (hsb : (3 * N < n → b₁ + b₂ + b₃ = 3 * N) ∧ ((n : ℕ∞) < 3 * N → b₁ + b₂ + b₃ = n) ∧
      (3 * N = n → (n : ℕ∞) ≤ b₁ + b₂ + b₃)) :
    iotaN n a₁ b₁ + iotaN n a₂ b₂ + iotaN n a₃ b₃ = 0 := by
  rcases lt_or_ge (n : ℕ∞) (3 * N) with hlt | hge
  ·
    have e := hsb.2.1 hlt
    have hb : ∀ {b : ℕ∞}, b ≤ b₁ + b₂ + b₃ → b ≠ ⊤ := fun h ht => by
      rw [e, ht] at h; simp at h
    have key : ∀ {a b m : ℕ∞}, ((a < b ∧ a = N ∧ m = N) ∨ (b ≤ a ∧ b = min m N)) →
        (a < b → (n : ℕ∞) < 3 * N → a + b = n) → b ≠ ⊤ → iotaN n a b = ((b.toNat : ℕ) : ZMod n) := by
      intro a b m c s hbt
      rcases c with ⟨hab, ha, -⟩ | ⟨hba, -⟩
      · rw [iotaN_of_lt hab]
        have h1 := s hab hlt
        have hat : a ≠ ⊤ := hab.ne_top
        lift a to ℕ using hat
        lift b to ℕ using hbt
        simp only [ENat.toNat_natCast]
        have h2 : a + b = n := by exact_mod_cast h1
        rw [neg_eq_iff_add_eq_zero, ← Nat.cast_add, show a + b = n by omega, ZMod.natCast_self]
      · rw [iotaN_of_le hba]
    have hb₁ : b₁ ≠ ⊤ := hb (by rw [add_assoc]; exact le_self_add)
    have hb₂ : b₂ ≠ ⊤ := hb (by rw [add_comm b₁, add_assoc]; exact le_self_add)
    have hb₃ : b₃ ≠ ⊤ := hb le_add_self
    rw [key c₁ s₁ hb₁, key c₂ s₂ hb₂, key c₃ s₃ hb₃]
    lift b₁ to ℕ using hb₁
    lift b₂ to ℕ using hb₂
    lift b₃ to ℕ using hb₃
    simp only [ENat.toNat_natCast]
    have : b₁ + b₂ + b₃ = n := by exact_mod_cast e
    rw [← Nat.cast_add, ← Nat.cast_add, this, ZMod.natCast_self]
  · have hNt : N ≠ ⊤ := by rintro rfl; simp at hge
    lift N to ℕ using hNt
    have hN1 : 1 ≤ N := by exact_mod_cast hN
    have h3 : 3 * N ≤ n := by exact_mod_cast hge
    have em := hsm (by exact_mod_cast (show 2 * N < n by omega))
    have hm₁t : m₁ ≠ ⊤ := by rintro rfl; simp at em; exact absurd em (top_ne_two_mul N)
    have hm₂t : m₂ ≠ ⊤ := by rintro rfl; simp at em; exact absurd em (top_ne_two_mul N)
    have hm₃t : m₃ ≠ ⊤ := by rintro rfl; simp at em; exact absurd em (top_ne_two_mul N)
    lift m₁ to ℕ using hm₁t
    lift m₂ to ℕ using hm₂t
    lift m₃ to ℕ using hm₃t
    have em' : m₁ + m₂ + m₃ = 2 * N := by exact_mod_cast em
    have h1 : 1 ≤ m₁ := by exact_mod_cast hm₁
    have h2 : 1 ≤ m₂ := by exact_mod_cast hm₂
    have h3' : 1 ≤ m₃ := by exact_mod_cast hm₃
    have hb3 : 3 * N ≤ b₁ + b₂ + b₃ := by
      rcases lt_or_eq_of_le h3 with h | h
      · rw [hsb.1 (by exact_mod_cast h)]
      · have := hsb.2.2 (by exact_mod_cast h)
        rw [← h] at this; exact_mod_cast this
    have mincast : ∀ m : ℕ, min (m : ℕ∞) (N : ℕ∞) = ((min m N : ℕ) : ℕ∞) := fun m => by
      norm_cast
    rcases c₁ with ⟨l₁, a₁e, m₁e⟩ | ⟨l₁, b₁e⟩ <;> rcases c₂ with ⟨l₂, a₂e, m₂e⟩ | ⟨l₂, b₂e⟩ <;>
      rcases c₃ with ⟨l₃, a₃e, m₃e⟩ | ⟨l₃, b₃e⟩
    · have : m₁ = N := by exact_mod_cast m₁e
      have : m₂ = N := by exact_mod_cast m₂e
      omega
    · have : m₁ = N := by exact_mod_cast m₁e
      have : m₂ = N := by exact_mod_cast m₂e
      omega
    · have : m₁ = N := by exact_mod_cast m₁e
      have : m₃ = N := by exact_mod_cast m₃e
      omega
    · have hm1 : m₁ = N := by exact_mod_cast m₁e
      rw [iotaN_of_lt l₁, iotaN_of_le l₂, iotaN_of_le l₃, a₁e, b₂e, b₃e, mincast, mincast]
      simp only [ENat.toNat_natCast]
      rw [show min m₂ N = m₂ by omega, show min m₃ N = m₃ by omega, add_assoc, neg_add_eq_zero,
        ← Nat.cast_add, show m₂ + m₃ = N by omega]
    · have : m₂ = N := by exact_mod_cast m₂e
      have : m₃ = N := by exact_mod_cast m₃e
      omega
    · have hm2 : m₂ = N := by exact_mod_cast m₂e
      rw [iotaN_of_le l₁, iotaN_of_lt l₂, iotaN_of_le l₃, a₂e, b₁e, b₃e, mincast, mincast]
      simp only [ENat.toNat_natCast]
      rw [show min m₁ N = m₁ by omega, show min m₃ N = m₃ by omega, add_right_comm,
        add_neg_eq_zero, ← Nat.cast_add, show m₁ + m₃ = N by omega]
    · have hm3 : m₃ = N := by exact_mod_cast m₃e
      rw [iotaN_of_le l₁, iotaN_of_le l₂, iotaN_of_lt l₃, a₃e, b₁e, b₂e, mincast, mincast]
      simp only [ENat.toNat_natCast]
      rw [show min m₁ N = m₁ by omega, show min m₂ N = m₂ by omega, add_neg_eq_zero,
        ← Nat.cast_add, show m₁ + m₂ = N by omega]
    · exfalso
      rw [b₁e, b₂e, b₃e, mincast, mincast, mincast] at hb3
      have : 3 * N ≤ min m₁ N + min m₂ N + min m₃ N := by exact_mod_cast hb3
      omega

section Val

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {π : 𝒪}
  (hπ : Irreducible π)

local notation "v" => addVal 𝒪

theorem v_unit {u : 𝒪} (hu : IsUnit u) : v u = 0 := addVal_eq_zero_iff.2 hu

theorem v_mul_unit_left {u a : 𝒪} (hu : IsUnit u) : v (u * a) = v a := by
  rw [addVal_mul, v_unit hu, zero_add]

theorem v_ne_top {a : 𝒪} (ha : a ≠ 0) : v a ≠ ⊤ := fun h => ha (addVal_eq_top_iff.1 h)

theorem v_cube (a : 𝒪) : v (a ^ 3) = 3 * v a := by
  rw [addVal_pow, nsmul_eq_mul]; rfl

include hπ in
theorem one_le_v_iff {a : 𝒪} : 1 ≤ v a ↔ π ∣ a := by
  rw [← addVal_uniformizer hπ, addVal_le_iff_dvd]

theorem v_cube_add (z q : 𝒪) :
    (3 * v z < v q → v (z ^ 3 + q) = 3 * v z) ∧ (v q < 3 * v z → v (z ^ 3 + q) = v q) ∧
      (3 * v z = v q → v q ≤ v (z ^ 3 + q)) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [AddValuation.map_add_eq_of_lt_left _ (by rwa [v_cube]), v_cube]
  · rw [AddValuation.map_add_eq_of_lt_right _ (by rwa [v_cube])]
  · have := AddValuation.map_add (addVal 𝒪) (z ^ 3) q
    rwa [v_cube, h, min_self] at this

variable {e q : 𝒪}

theorem v_sum_eq {x y : 𝒪} (h : y * (y + e * x) = x ^ 3 + q) : v y + v (y + e * x) = v (x ^ 3 + q) := by
  rw [← addVal_mul, h]

theorem v_x_of {x y : 𝒪} (he : IsUnit e) :
    min (v y) (v (y + e * x)) ≤ v x ∧ (v y ≠ v (y + e * x) → v x = min (v y) (v (y + e * x))) := by
  have hx : v x = v ((y + e * x) + -y) := by
    rw [show (y + e * x) + -y = e * x by ring, v_mul_unit_left he]
  refine ⟨?_, fun hne => ?_⟩
  · rw [hx, min_comm]
    have := AddValuation.map_add (addVal 𝒪) (y + e * x) (-y)
    rwa [AddValuation.map_neg] at this
  · rw [hx, AddValuation.map_add_of_distinct_val _ (by rwa [AddValuation.map_neg, ne_comm]),
      AddValuation.map_neg, min_comm]

include hπ in

theorem tie_two {x y : 𝒪} (he : IsUnit e) (hq : q ≠ 0) (h : y * (y + e * x) = x ^ 3 + q)
    (dy : π ∣ y) (ht : v y = v (y + e * x)) : 2 * v y = v q := by
  have hs := v_sum_eq h
  obtain ⟨hmin, -⟩ := v_x_of (x := x) (y := y) he
  rw [← ht, min_self] at hmin
  rw [← ht] at hs
  have hy1 : 1 ≤ v y := (one_le_v_iff hπ).2 dy
  have hqt := v_ne_top hq
  obtain ⟨c1, c2, c3⟩ := v_cube_add x q
  rcases lt_trichotomy (3 * v x) (v q) with h3 | h3 | h3
  · exfalso
    rw [c1 h3] at hs
    have hxt : v x ≠ ⊤ := by
      rintro hx; rw [hx] at h3; simp at h3
    have hyt : v y ≠ ⊤ := ne_top_of_le_ne_top hxt hmin
    lift v x to ℕ using hxt with m hm
    lift v y to ℕ using hyt with a ha
    have e1 : a + a = 3 * m := by exact_mod_cast hs
    have e2 : a ≤ m := by exact_mod_cast hmin
    have e3 : 1 ≤ a := by exact_mod_cast hy1
    omega
  · exfalso
    have hs' := c3 h3
    rw [← hs, ← h3] at hs'
    have hxt : v x ≠ ⊤ := by
      rintro hx; rw [hx] at h3; exact hqt (by rw [← h3]; simp)
    have hyt : v y ≠ ⊤ := ne_top_of_le_ne_top hxt hmin
    lift v x to ℕ using hxt with m hm
    lift v y to ℕ using hyt with a ha
    have e1 : 3 * m ≤ a + a := by exact_mod_cast hs'
    have e2 : a ≤ m := by exact_mod_cast hmin
    have e3 : 1 ≤ a := by exact_mod_cast hy1
    omega
  · rw [c2 h3] at hs
    rw [two_mul, hs]

end Val

section Alg

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {π : 𝒪}
  (hπ : Irreducible π)

local notation "v" => addVal 𝒪

variable {e q : 𝒪}

theorem v_sq (a : 𝒪) : v (a ^ 2) = v a + v a := by rw [pow_two, addVal_mul]

include hπ in

theorem iota_pair {μ l l' ρ ρ' U U' xP yP xR yR : 𝒪} (he : IsUnit e) (hq : q ≠ 0)
    (hl : IsUnit l) (hl' : IsUnit l') (hU : IsUnit U) (hU' : IsUnit U') (hμ : μ ≠ 0)
    (eP : yP * (yP + e * xP) = xP ^ 3 + q) (eR : yR * (yR + e * xR) = xR ^ 3 + q)
    (dxP : π ∣ xP) (dyP : π ∣ yP) (dyR : π ∣ yR)
    (lP : μ * yP = l * (xP + ρ)) (lP' : μ * (yP + e * xP) = l' * (xP + ρ'))
    (lR : μ * yR = l * (xR + ρ)) (lR' : μ * (yR + e * xR) = l' * (xR + ρ'))
    (pα : μ ^ 2 * (q - ρ ^ 3) = (xP + ρ) * (xR + ρ) * U)
    (pβ : μ ^ 2 * (q - ρ' ^ 3) = (xP + ρ') * (xR + ρ') * U')
    (hll : l' - l = e * μ) (hρρ : l * ρ = l' * ρ') :
    iotaN (v q).toNat (v yP) (v (yP + e * xP)) + iotaN (v q).toNat (v yR) (v (yR + e * xR)) = 0 := by
  have hn : v q = ((v q).toNat : ℕ∞) := (ENat.natCast_toNat (v_ne_top hq)).symm
  set n := (v q).toNat
  have hf : v μ ≠ ⊤ := v_ne_top hμ
  have hD : ∀ {x y : 𝒪}, μ * y = l * (x + ρ) → v (x + ρ) = v μ + v y := fun h => by
    rw [← addVal_mul, h, v_mul_unit_left hl]
  have hD' : ∀ {x y : 𝒪}, μ * (y + e * x) = l' * (x + ρ') → v (x + ρ') = v μ + v (y + e * x) :=
    fun h => by rw [← addVal_mul, h, v_mul_unit_left hl']
  have hρ' : v ρ' = v ρ := by
    have := congrArg v hρρ
    rwa [v_mul_unit_left hl, v_mul_unit_left hl', eq_comm] at this
  have hdiff : v ((xP + ρ) + -(xP + ρ')) = v μ + v ρ := by
    have h1 : l * ((xP + ρ) + -(xP + ρ')) = e * (μ * ρ') := by linear_combination hρρ + ρ' * hll
    have := congrArg v h1
    rwa [v_mul_unit_left hl, v_mul_unit_left he, addVal_mul, hρ'] at this
  have hdiffR : v ((xR + ρ) + -(xR + ρ')) = v μ + v ρ := by
    rw [show (xR + ρ) + -(xR + ρ') = (xP + ρ) + -(xP + ρ') by ring, hdiff]
  have hτ1 : 1 ≤ v ρ := by
    rw [one_le_v_iff hπ]
    have h1 : π ∣ l * (xP + ρ) := by rw [← lP]; exact dvd_mul_of_dvd_right dyP μ
    have h2 : π ∣ xP + ρ := (hl.dvd_mul_left).1 h1
    have := dvd_sub h2 dxP
    rwa [add_sub_cancel_left] at this

  have cls : ∀ {x y : 𝒪}, y * (y + e * x) = x ^ 3 + q → π ∣ y → μ * y = l * (x + ρ) →
      μ * (y + e * x) = l' * (x + ρ') → v ((x + ρ) + -(x + ρ')) = v μ + v ρ →
      (v y = v (y + e * x) ∧ 2 * v y = n) ∨
        (v y ≠ v (y + e * x) ∧ min (v y) (v (y + e * x)) = v ρ) := by
    intro x y h dy l1 l2 hd
    by_cases ht : v y = v (y + e * x)
    · exact Or.inl ⟨ht, by rw [tie_two hπ he hq h dy ht, hn]⟩
    · refine Or.inr ⟨ht, ?_⟩
      have hne : v (x + ρ) ≠ v (-(x + ρ')) := by
        rw [AddValuation.map_neg, hD l1, hD' l2]
        exact fun h' => ht (ENat.add_right_injective_of_ne_top hf h')
      rw [AddValuation.map_add_of_distinct_val _ hne, AddValuation.map_neg, hD l1, hD' l2,
        min_add_add_left] at hd
      exact ENat.add_right_injective_of_ne_top hf hd
  have sums : ∀ {x y : 𝒪}, y * (y + e * x) = x ^ 3 + q →
      min (v y) (v (y + e * x)) = v ρ → v y ≠ v (y + e * x) →
      (3 * v ρ < n → v y + v (y + e * x) = 3 * v ρ) ∧ (n < 3 * v ρ → v y + v (y + e * x) = n) := by
    intro x y h hm hne
    have hx := (v_x_of (x := x) (y := y) he).2 hne
    rw [hm] at hx
    obtain ⟨c1, c2, -⟩ := v_cube_add x q
    rw [hn] at c1 c2
    rw [v_sum_eq h, ← hx]
    exact ⟨c1, c2⟩
  have prod : ∀ {r : 𝒪} {W : 𝒪}, IsUnit W → μ ^ 2 * (q - r ^ 3) = (xP + r) * (xR + r) * W →
      v (q - r ^ 3) + (v μ + v μ) = v (xP + r) + v (xR + r) := by
    intro r W hW h
    have := congrArg v h
    rw [addVal_mul, addVal_mul, addVal_mul, v_unit hW, add_zero, v_sq, add_comm] at this
    exact this
  have hα := prod hU pα
  have hβ := prod hU' pβ
  rw [hD lP, hD lR] at hα
  rw [hD' lP', hD' lR'] at hβ
  have h2f : v μ + v μ ≠ ⊤ := by
    rw [Ne, ENat.add_eq_top]; exact fun h => h.elim hf hf
  have hα' : v (q - ρ ^ 3) = v yP + v yR := by
    apply ENat.add_left_injective_of_ne_top h2f
    show v (q - ρ ^ 3) + (v μ + v μ) = (v yP + v yR) + (v μ + v μ)
    rw [hα]; ring
  have hβ' : v (q - ρ' ^ 3) = v (yP + e * xP) + v (yR + e * xR) := by
    apply ENat.add_left_injective_of_ne_top h2f
    show v (q - ρ' ^ 3) + (v μ + v μ) = (v (yP + e * xP) + v (yR + e * xR)) + (v μ + v μ)
    rw [hβ]; ring
  have cube : ∀ r : 𝒪, (3 * v r < n → v (q - r ^ 3) = 3 * v r) ∧ (n < 3 * v r → v (q - r ^ 3) = n) ∧
      (3 * v r = n → n ≤ v (q - r ^ 3)) := by
    intro r
    have h := v_cube_add (-r) q
    rw [AddValuation.map_neg, show (-r) ^ 3 + q = q - r ^ 3 by ring, hn] at h
    exact h
  refine iotaN_two hτ1 (cls eP dyP lP lP' hdiff) (cls eR dyR lR lR' hdiffR)
    (fun hne => sums eP (((cls eP dyP lP lP' hdiff).resolve_left fun h => hne h.1).2) hne)
    (fun hne => sums eR (((cls eR dyR lR lR' hdiffR).resolve_left fun h => hne h.1).2) hne)
    ?_ ?_
  · rw [← hα']; exact cube ρ
  · have hc := cube ρ'
    rw [hρ'] at hc
    rw [← hβ']; exact hc

include hπ in

theorem point_kind {ℓ ν x y : 𝒪} (hq : q ≠ 0) (hℓ : π ∣ ℓ) (hℓe : IsUnit (ℓ + e))
    (h : y * (y + e * x) = x ^ 3 + q) (l : y = ℓ * x + ν) :
    (v y < v (y + e * x) ∧ v y = v ν ∧ v x = v ν) ∨
      (v (y + e * x) ≤ v y ∧ v (y + e * x) = min (v x) (v ν)) := by
  have hw : y + e * x = (ℓ + e) * x + ν := by rw [l]; ring
  have hwx : v ((ℓ + e) * x) = v x := v_mul_unit_left hℓe
  have hℓx : v x + 1 ≤ v (ℓ * x) := by
    rw [addVal_mul, add_comm]; exact add_le_add_left ((one_le_v_iff hπ).2 hℓ) _
  rw [hw, l]
  rcases lt_trichotomy (v x) (v ν) with hm | hm | hm
  · have hxt : v x ≠ ⊤ := hm.ne_top
    have hb : v ((ℓ + e) * x + ν) = v x := by
      rw [AddValuation.map_add_eq_of_lt_left _ (by rwa [hwx]), hwx]
    have ha : v x < v (ℓ * x + ν) := by
      have hlt : v x < v (ℓ * x) := lt_of_lt_of_le (ENat.lt_add_one_iff hxt |>.2 le_rfl) hℓx
      exact lt_of_lt_of_le (lt_min hlt hm) (AddValuation.map_add _ _ _)
    right
    rw [hb, min_eq_left hm.le]
    exact ⟨ha.le, rfl⟩
  · have hNt : v x ≠ ⊤ := by
      intro ht
      have hx0 : x = 0 := addVal_eq_top_iff.1 ht
      have hν0 : ν = 0 := addVal_eq_top_iff.1 (hm ▸ ht)
      subst hx0 hν0
      apply hq
      rw [l] at h
      simpa [eq_comm] using h
    have ha : v (ℓ * x + ν) = v ν := by
      rw [AddValuation.map_add_eq_of_lt_right]
      rw [← hm]
      exact lt_of_lt_of_le (ENat.lt_add_one_iff hNt |>.2 le_rfl) hℓx
    have hb : v ν ≤ v ((ℓ + e) * x + ν) := by
      have := AddValuation.map_add (addVal 𝒪) ((ℓ + e) * x) ν
      rwa [hwx, hm, min_self] at this
    rcases eq_or_lt_of_le hb with hb' | hb'
    · right
      rw [← hb', ha, hm, min_self]
      exact ⟨le_rfl, rfl⟩
    · left
      rw [ha]
      exact ⟨hb', rfl, hm⟩
  · have hb : v ((ℓ + e) * x + ν) = v ν := by
      rw [AddValuation.map_add_eq_of_lt_right _ (by rwa [hwx])]
    have ha : v (ℓ * x + ν) = v ν := by
      rw [AddValuation.map_add_eq_of_lt_right]
      exact lt_of_lt_of_le hm (le_trans le_self_add hℓx)
    right
    rw [hb, ha, min_eq_right hm.le]
    exact ⟨le_rfl, rfl⟩

include hπ in

theorem iota_triple {ℓ ν x₁ y₁ x₂ y₂ x₃ y₃ : 𝒪} (hq : q ≠ 0) (hℓ : π ∣ ℓ)
    (hℓe : IsUnit (ℓ + e))
    (e₁ : y₁ * (y₁ + e * x₁) = x₁ ^ 3 + q) (e₂ : y₂ * (y₂ + e * x₂) = x₂ ^ 3 + q)
    (e₃ : y₃ * (y₃ + e * x₃) = x₃ ^ 3 + q)
    (dx₁ : π ∣ x₁) (dx₂ : π ∣ x₂) (dx₃ : π ∣ x₃) (dy₁ : π ∣ y₁)
    (l₁ : y₁ = ℓ * x₁ + ν) (l₂ : y₂ = ℓ * x₂ + ν) (l₃ : y₃ = ℓ * x₃ + ν)
    (hv3 : x₁ * x₂ * x₃ = ν ^ 2 - q)
    (hvw : (y₁ + e * x₁) * (y₂ + e * x₂) * (y₃ + e * x₃) = ν ^ 3 - (ℓ + e) ^ 3 * q) :
    iotaN (v q).toNat (v y₁) (v (y₁ + e * x₁)) + iotaN (v q).toNat (v y₂) (v (y₂ + e * x₂)) +
      iotaN (v q).toNat (v y₃) (v (y₃ + e * x₃)) = 0 := by
  have hn : v q = ((v q).toNat : ℕ∞) := (ENat.natCast_toNat (v_ne_top hq)).symm
  set n := (v q).toNat
  have hN : 1 ≤ v ν := by
    rw [one_le_v_iff hπ]
    have : ν = y₁ - ℓ * x₁ := by rw [l₁]; ring
    rw [this]; exact dvd_sub dy₁ (dvd_mul_of_dvd_left hℓ _)
  have sA : ∀ {x y : 𝒪}, y * (y + e * x) = x ^ 3 + q →
      (v y < v (y + e * x) ∧ v y = v ν ∧ v x = v ν) ∨
        (v (y + e * x) ≤ v y ∧ v (y + e * x) = min (v x) (v ν)) →
      v y < v (y + e * x) → (n : ℕ∞) < 3 * v ν → v y + v (y + e * x) = n := by
    intro x y h c hlt hn3
    rcases c with ⟨-, -, hx⟩ | ⟨hle, -⟩
    · rw [v_sum_eq h, (v_cube_add x q).2.1 (by rw [hx, hn]; exact hn3), hn]
    · exact absurd hle (not_le.2 hlt)
  have k₁ := point_kind hπ hq hℓ hℓe e₁ l₁
  have k₂ := point_kind hπ hq hℓ hℓe e₂ l₂
  have k₃ := point_kind hπ hq hℓ hℓe e₃ l₃
  refine iotaN_three hN k₁ k₂ k₃ ((one_le_v_iff hπ).2 dx₁) ((one_le_v_iff hπ).2 dx₂)
    ((one_le_v_iff hπ).2 dx₃) (sA e₁ k₁) (sA e₂ k₂) (sA e₃ k₃) ?_ ?_
  · intro h2
    rw [← addVal_mul, ← addVal_mul, hv3, sub_eq_add_neg,
      AddValuation.map_add_eq_of_lt_left _ (by rwa [AddValuation.map_neg, v_sq, ← two_mul, hn]),
      v_sq, two_mul]
  · rw [← addVal_mul, ← addVal_mul, hvw]
    have hq3 : v ((ℓ + e) ^ 3 * q) = n := by
      rw [addVal_mul, show (ℓ + e) ^ 3 = (ℓ + e) ^ 3 by rfl, v_unit (hℓe.pow 3), zero_add, hn]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [sub_eq_add_neg, AddValuation.map_add_eq_of_lt_left _ (by rwa [AddValuation.map_neg, hq3,
        v_cube]), v_cube]
    · rw [sub_eq_add_neg, AddValuation.map_add_eq_of_lt_right _ (by rwa [AddValuation.map_neg, hq3,
        v_cube]), AddValuation.map_neg, hq3]
    · have := AddValuation.map_sub (addVal 𝒪) (ν ^ 3) ((ℓ + e) ^ 3 * q)
      rwa [v_cube, hq3, h, min_self] at this

end Alg

end

end GroundTheory.Arith.Abelian
