import Mathlib
import GroundTheory.AutomorphicForms.HermitianClassification
import GroundTheory.AutomorphicForms.HermitianNormLocal
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe

noncomputable section

namespace GroundTheory.Automorphic

open GroundTheory.LocalField ValuativeRel

section Field

variable {F : Type*} [Field F]

def SqNorm (s u : F) : Prop := ∃ x y : F, x ^ 2 - s * y ^ 2 = u

theorem sqNorm_sq (s : F) (x : F) : SqNorm s (x ^ 2) := ⟨x, 0, by ring⟩

theorem SqNorm.mul {s a b : F} (ha : SqNorm s a) (hb : SqNorm s b) : SqNorm s (a * b) := by
  obtain ⟨x, y, rfl⟩ := ha
  obtain ⟨z, w, rfl⟩ := hb
  exact ⟨x * z + s * y * w, x * w + y * z, by ring⟩

theorem SqNorm.inv {s a : F} (ha : SqNorm s a) : SqNorm s a⁻¹ := by
  by_cases h0 : a = 0
  · rw [h0, inv_zero]; exact ⟨0, 0, by ring⟩
  obtain ⟨x, y, rfl⟩ := ha
  refine ⟨x / (x ^ 2 - s * y ^ 2), y / (x ^ 2 - s * y ^ 2), ?_⟩
  field_simp

theorem SqNorm.map {F' : Type*} [Field F'] (φ : F →+* F') {s u : F} (h : SqNorm s u) :
    SqNorm (φ s) (φ u) := by
  obtain ⟨x, y, rfl⟩ := h
  exact ⟨φ x, φ y, by simp [map_sub, map_mul, map_pow]⟩

variable (h2 : (2 : F) ≠ 0)
include h2

theorem sqNorm_of_eq_sq {s r : F} (hs : s = r ^ 2) (hr : r ≠ 0) (u : F) : SqNorm s u := by
  refine ⟨(1 + u) / 2, (u - 1) / (2 * r), ?_⟩
  rw [hs]
  field_simp
  ring

theorem SqNorm.symm {s u : F} (hu : u ≠ 0) (h : SqNorm s u) : SqNorm u s := by
  obtain ⟨x, y, hxy⟩ := h
  by_cases hy : y = 0
  · subst hy
    have hux : u = x ^ 2 := by rw [← hxy]; ring
    have hx : x ≠ 0 := by
      rintro rfl
      exact hu (by rw [hux]; ring)
    exact sqNorm_of_eq_sq h2 hux hx s
  · refine ⟨x / y, 1 / y, ?_⟩
    field_simp
    rw [← hxy]
    ring

theorem sqNorm_comm {s u : F} (hs : s ≠ 0) (hu : u ≠ 0) : SqNorm s u ↔ SqNorm u s :=
  ⟨SqNorm.symm h2 hu, SqNorm.symm h2 hs⟩

end Field

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]

theorem exists_index_two {s : F} (hs : ∀ r : F, r ^ 2 ≠ s) :
    ∃ N : Subgroup Fˣ, Nat.card (Fˣ ⧸ N) = 2 ∧ ∀ u : Fˣ, u ∈ N ↔ SqNorm s (u : F) := by
  have : Fact (∀ r : F, r ^ 2 ≠ s + 0 * r) := ⟨by simpa using hs⟩
  have : Algebra.IsQuadraticExtension F (QuadraticAlgebra F s 0) :=
    ⟨QuadraticAlgebra.finrank_eq_two s 0⟩
  refine ⟨(normUnits F (QuadraticAlgebra F s 0)).range, natCard_quotient_range_normUnits_eq_two,
    fun u => ?_⟩
  rw [mem_range_normUnits_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.re, z.im, by rw [← algebraNorm_quadraticAlgebra, hz]⟩
  · rintro ⟨x, y, h⟩
    exact ⟨⟨x, y⟩, by rw [algebraNorm_quadraticAlgebra]; exact h⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] in

theorem le_of_le_of_natCard_eq_two {G : Type*} [CommGroup G] {A B : Subgroup G}
    (hA : Nat.card (G ⧸ A) = 2) (hB : Nat.card (G ⧸ B) = 2) (hAB : A ≤ B) : B ≤ A := by
  intro b hb
  by_contra hbA
  have hBtop : B ≠ ⊤ := by
    rintro rfl
    have : Nat.card (G ⧸ (⊤ : Subgroup G)) = 1 := Subgroup.index_top
    omega
  obtain ⟨g, hg⟩ : ∃ g, g ∉ B := by
    by_contra H
    push Not at H
    exact hBtop (eq_top_iff.2 fun g _ => H g)
  have hgA : g ∉ A := fun h => hg (hAB h)
  rcases mem_or_mul_inv_mem_of_natCard_eq_two hA hbA g with h | h
  · exact hgA h
  · exact hg (by simpa using B.mul_mem (hAB h) hb)

theorem sqNorm_of_quadratic {F' : Type*} [Field F'] (φ : F →+* F') {e : F}
    (he : ∀ r : F, r ^ 2 ≠ e) {s : F'} (hs : s ^ 2 = φ e) {d β : F} (hd : d ≠ 0)
    (hβ : β ≠ 0) : SqNorm (φ d) (φ β) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have h2' : (2 : F') ≠ 0 := by rw [← map_ofNat φ 2]; exact (map_ne_zero φ).2 h2
  have he0 : e ≠ 0 := fun h => he 0 (by rw [h]; ring)

  by_cases hdsq : ∃ r : F, r ^ 2 = d
  · obtain ⟨r, rfl⟩ := hdsq
    have hr : r ≠ 0 := by rintro rfl; exact hd (by ring)
    exact sqNorm_of_eq_sq h2' (by rw [map_pow]) ((map_ne_zero φ).2 hr) _
  by_cases hdesq : ∃ r : F, r ^ 2 = d * e
  · obtain ⟨r, hr⟩ := hdesq
    have hr0 : r ≠ 0 := by rintro rfl; exact mul_ne_zero hd he0 (by rw [← hr]; ring)
    have hφe : φ e ≠ 0 := (map_ne_zero φ).2 he0
    refine sqNorm_of_eq_sq h2' (r := φ r * s / φ e) ?_ ?_ _
    · field_simp
      rw [hs, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hr]
      ring
    · have hs0 : s ≠ 0 := by
        rintro rfl
        exact hφe (by rw [← hs]; ring)
      exact div_ne_zero (mul_ne_zero ((map_ne_zero φ).2 hr0) hs0) hφe
  push Not at hdsq hdesq
  by_cases hβd : SqNorm d β
  · exact hβd.map φ
  obtain ⟨Nd, hNd, hmemd⟩ := exists_index_two hdsq
  obtain ⟨Nde, hNde, hmemde⟩ := exists_index_two hdesq
  obtain ⟨Ne, hNe, hmeme⟩ := exists_index_two he
  have hde0 : d * e ≠ 0 := mul_ne_zero hd he0

  obtain ⟨n, hnde, hnd⟩ : ∃ n : Fˣ, n ∈ Nde ∧ n ∉ Nd := by
    by_contra H
    push Not at H
    have hle : Nd ≤ Nde := le_of_le_of_natCard_eq_two hNde hNd H

    have key : ∀ b : Fˣ, SqNorm (b : F) e := by
      intro b
      by_cases hbsq : ∃ r : F, r ^ 2 = b
      · obtain ⟨r, hr⟩ := hbsq
        have hr0 : r ≠ 0 := by rintro rfl; exact b.ne_zero (by rw [← hr]; ring)
        exact sqNorm_of_eq_sq h2 hr.symm hr0 e
      push Not at hbsq
      obtain ⟨Nb, hNb, hmemb⟩ := exists_index_two hbsq
      have hiff : Units.mk0 d hd ∈ Nb ↔ Units.mk0 (d * e) hde0 ∈ Nb := by
        rw [hmemb, hmemb, Units.val_mk0, Units.val_mk0, sqNorm_comm h2 b.ne_zero hd,
          sqNorm_comm h2 b.ne_zero hde0, ← hmemd b, ← hmemde b]
        exact ⟨fun h => hle h, fun h => H _ h⟩
      have hem : Units.mk0 e he0 ∈ Nb := by
        have hq : Units.mk0 (d * e) hde0 * (Units.mk0 d hd)⁻¹ = Units.mk0 e he0 := by
          apply Units.ext
          simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
          field_simp
        by_cases hdb : Units.mk0 d hd ∈ Nb
        · rw [← hq]
          exact Nb.mul_mem (hiff.1 hdb) (Nb.inv_mem hdb)
        · rcases mem_or_mul_inv_mem_of_natCard_eq_two hNb hdb (Units.mk0 (d * e) hde0) with h | h
          · exact absurd (hiff.2 h) hdb
          · rwa [hq] at h
      simpa using (hmemb _).1 hem
    have htop : Ne = ⊤ := by
      refine eq_top_iff.2 fun b _ => (hmeme b).2 ?_
      exact (key b).symm h2 he0
    rw [htop] at hNe
    have : Nat.card (Fˣ ⧸ (⊤ : Subgroup Fˣ)) = 1 := Subgroup.index_top
    omega

  have hβNd : Units.mk0 β hβ ∉ Nd := fun h => hβd (by simpa using (hmemd _).1 h)
  have hq : Units.mk0 β hβ * n⁻¹ ∈ Nd :=
    (mem_or_mul_inv_mem_of_natCard_eq_two hNd hnd (Units.mk0 β hβ)).resolve_left hβNd
  obtain ⟨a, b, hab⟩ := (hmemd _).1 hq
  obtain ⟨c, f, hcf⟩ := (hmemde _).1 hnde
  have h1 : SqNorm (φ d) (φ ((Units.mk0 β hβ * n⁻¹ : Fˣ) : F)) := SqNorm.map φ ⟨a, b, hab⟩
  have h2n : SqNorm (φ d) (φ (n : F)) := by
    refine ⟨φ c, φ f * s, ?_⟩
    rw [← hcf, mul_pow, hs]
    simp only [map_sub, map_mul, map_pow]
    ring
  have := h1.mul h2n
  rwa [← map_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, mul_assoc,
    inv_mul_cancel₀ n.ne_zero, mul_one] at this

end Local

end GroundTheory.Automorphic
