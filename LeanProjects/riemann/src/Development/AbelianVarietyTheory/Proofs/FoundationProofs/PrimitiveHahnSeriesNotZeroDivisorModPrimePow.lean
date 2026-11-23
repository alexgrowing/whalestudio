import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesInvertibleModPrimePowStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory

theorem primCan_mul_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (c : Ω) (a b : HahnSeries ℚ Ω)
    (ha : ∀ r, a.coeff r ∈ A) (hb : ∀ r, ∃ z ∈ A, b.coeff r = c * z) :
    ∀ r, ∃ z ∈ A, (a * b).coeff r = c * z := by
  intro r
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => ∃ z ∈ A, x = c * z) ?_ ?_ ?_
  · rintro x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨z + w, A.add_mem _ _ hz hw, by ring⟩
  · exact ⟨0, A.zero_mem, by simp⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hb ij.2
    exact ⟨a.coeff ij.1 * z, A.mul_mem _ _ (ha _) hz, by rw [e]; ring⟩

theorem primCan : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
    ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P φ : HahnSeries ℚ Ω), 0 < L → Prim A P →
    (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → (∀ r, φ.coeff r ∈ A) →
    (∀ r, CgA A l n ((φ * P).coeff r) 0) → ∀ r, CgA A l n (φ.coeff r) 0 := by
  intro Ω _ _ _ l _ A hl n L P φ hL hP hden hφ hφP
  obtain ⟨Q, hQ, -, hQP⟩ := GlobalTheory.T.primitive_hahnSeries_invertible_mod_prime_pow l A hl n L P hL hP hden
  have h1 : ∀ r, ∃ z ∈ A, (Q * P - 1).coeff r = (l : Ω) ^ n * z := by
    intro r
    obtain ⟨z, hz, e⟩ := hQP r
    exact ⟨z, hz, by rw [HahnSeries.coeff_sub]; exact e⟩
  have h2 := primCan_mul_dvd A _ φ _ hφ h1
  have h3 : ∀ r, ∃ z ∈ A, (Q * (φ * P)).coeff r = (l : Ω) ^ n * z := by
    refine primCan_mul_dvd A _ Q _ hQ ?_
    intro r
    obtain ⟨z, hz, e⟩ := hφP r
    exact ⟨z, hz, by rw [← e, sub_zero]⟩
  intro r
  obtain ⟨z, hz, ez⟩ := h3 r
  obtain ⟨w, hw, ew⟩ := h2 r
  have hid : φ = Q * (φ * P) - φ * (Q * P - 1) := by ring
  refine ⟨z - w, sub_mem hz hw, ?_⟩
  rw [sub_zero, hid, HahnSeries.coeff_sub, ez, ew]
  ring

end GlobalTheory
