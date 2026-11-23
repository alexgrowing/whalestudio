import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory

theorem inZl_of_twisted_difference {G : Type} [CommGroup G] [Finite G] (l : ℕ) [Fact l.Prime]
    (g : G) (q : ℕ) (hq : l ∣ q) (x : G → ℚ)
    (hx : ∀ C, InZl l (x C - (q : ℚ) * x (C * g))) : ∀ C, InZl l (x C) := by
  by_contra h
  push_neg at h
  obtain ⟨C0, hC0⟩ := h
  obtain ⟨C, hC⟩ := Finite.exists_max (fun C => ‖((x C : ℚ) : ℚ_[l])‖)
  have h0 : 1 < ‖((x C0 : ℚ) : ℚ_[l])‖ := by
    unfold InZl at hC0; push_neg at hC0; exact hC0
  have h1 : 1 < ‖((x C : ℚ) : ℚ_[l])‖ := lt_of_lt_of_le h0 (hC C0)
  have hqn : ‖((q : ℚ) : ℚ_[l])‖ < 1 := by
    rw [Rat.cast_natCast]
    exact Padic.norm_natCast_lt_one_iff.2 hq
  have hy : ‖(((x C - (q : ℚ) * x (C * g) : ℚ)) : ℚ_[l])‖ ≤ 1 := hx C
  have hsplit : ((x C : ℚ) : ℚ_[l]) =
      (((x C - (q : ℚ) * x (C * g) : ℚ)) : ℚ_[l]) + ((q : ℚ) : ℚ_[l]) * ((x (C * g) : ℚ) : ℚ_[l]) := by
    push_cast; ring
  have hprod : ‖((q : ℚ) : ℚ_[l]) * ((x (C * g) : ℚ) : ℚ_[l])‖ < ‖((x C : ℚ) : ℚ_[l])‖ := by
    rw [norm_mul]
    have hle : ‖((x (C * g) : ℚ) : ℚ_[l])‖ ≤ ‖((x C : ℚ) : ℚ_[l])‖ := hC (C * g)
    calc ‖((q : ℚ) : ℚ_[l])‖ * ‖((x (C * g) : ℚ) : ℚ_[l])‖
        ≤ ‖((q : ℚ) : ℚ_[l])‖ * ‖((x C : ℚ) : ℚ_[l])‖ :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ < 1 * ‖((x C : ℚ) : ℚ_[l])‖ :=
          mul_lt_mul_of_pos_right hqn (by linarith)
      _ = ‖((x C : ℚ) : ℚ_[l])‖ := one_mul _
  have hna := Padic.nonarchimedean (p := l)
    (((x C - (q : ℚ) * x (C * g) : ℚ)) : ℚ_[l]) (((q : ℚ) : ℚ_[l]) * ((x (C * g) : ℚ) : ℚ_[l]))
  rw [← hsplit] at hna
  rcases le_max_iff.1 hna with h2 | h2
  · linarith
  · linarith

example : ∀ {G : Type} [CommGroup G] [Finite G] (l : ℕ) [Fact l.Prime] (g : G) (q : ℕ), l ∣ q →
    ∀ x : G → ℚ, (∀ C, InZl l (x C - (q : ℚ) * x (C * g))) → ∀ C, InZl l (x C) :=
  @inZl_of_twisted_difference

end GlobalTheory
