import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UBoundOffTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VAddNonnegOfIsIntegral
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.LevelBudget

variable {D : D7} {L : SizeData₂ D}

theorem ETpi_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) :
    Formalism.MainNotions.product_first_zeroth_parts.ETpi D u ≤ 12 * D.R.f * L.sc.b := by
  have hb := GlobalTheory.HCEntries.one_le_b L
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  unfold Formalism.MainNotions.product_first_zeroth_parts.ETpi
  have hN := GlobalTheory.LevelLoss.N_le_b h P
  have hNe : (D.R.N D.R.m : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by unfold Ranks.N; push_cast; ring
  have r2 := (GlobalTheory.FockDegreeGap.ranks_le D).2
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h1 : ∑ τ : D.what₂.Tau, (Formalism.MainNotions.product_first_zeroth_parts.Wt D u τ : ℝ) ≤ D.R.f * (5 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun τ : D.what₂.Tau => (Formalism.MainNotions.product_first_zeroth_parts.Wt D u τ : ℝ)) _
      (fun τ _ => GlobalTheory.LevelLoss.Wtau_le h P hx u τ)
    rwa [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at this
  have h2 : ((Formalism.MainNotions.product_first_zeroth_parts.tops D).card : ℝ) ≤ D.R.f := by
    have := Finset.card_le_univ (Formalism.MainNotions.product_first_zeroth_parts.tops D)
    rw [D.what₂.card_Tau] at this
    exact_mod_cast this
  have h3 : ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) ≤ L.sc.b := by nlinarith
  have h4 : ((Formalism.MainNotions.product_first_zeroth_parts.tops D).card : ℝ) * (((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1)) ≤ D.R.f * L.sc.b :=
    mul_le_mul h2 h3 (by positivity) hf0
  have h5 : (D.R.f : ℝ) * D.R.N D.R.m ≤ D.R.f * L.sc.b :=
    mul_le_mul_of_nonneg_left (by linarith [Nat.cast_nonneg (α := ℝ) (D.R.N D.R.m)]) hf0
  have h6 : 0 ≤ (D.R.f : ℝ) * L.sc.b := by positivity
  nlinarith

theorem admissible_off_type_level_budget : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _ ⟨x₁, h1⟩
  refine ⟨max (12 * Fm.CTu) 0, max 2 x₁, le_max_right _ _, fun x hx0 hx i u => ⟨fun S hS => GlobalTheory.SeenHalf.seen_half Fm x hx i u S hS, ?_⟩⟩
  have a := ETpi_le (Fm.sizes x hx i) (Fm.params x hx i)
    (by rw [Fm.L_x x i hx]; exact (le_max_left _ _).trans hx0) u
  have b := (h1 x ((le_max_right _ _).trans hx0) i).2 u
  have hb := GlobalTheory.HCEntries.one_le_b (Fm.L x i)
  have hT : (1 : ℝ) ≤ (((Fm.D x i).mem u).A.T : ℝ) := by exact_mod_cast ((Fm.D x i).mem u).A.T_prime.one_le
  have hl : 0 ≤ Real.log (((Fm.D x i).mem u).A.T : ℝ) := Real.log_nonneg hT
  have e : (Fm.L x i).B0 = (Fm.D x i).R.f * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.L := rfl
  have hB : 0 ≤ (Fm.L x i).B0 := Formalism.MainNotions.WeightDegreeSizes.loss_bound_nonneg _
  calc Formalism.MainNotions.product_first_zeroth_parts.ETpi (Fm.D x i) u * Real.log (((Fm.D x i).mem u).A.T : ℝ)
      ≤ 12 * (Fm.D x i).R.f * (Fm.L x i).sc.b * Real.log (((Fm.D x i).mem u).A.T : ℝ) :=
        mul_le_mul_of_nonneg_right a hl
    _ ≤ 12 * (Fm.D x i).R.f * (Fm.L x i).sc.b * (Fm.CTu * (Fm.D x i).R.m * (Fm.L x i).sc.L) :=
        mul_le_mul_of_nonneg_left b (by positivity)
    _ = 12 * Fm.CTu * (Fm.L x i).B0 := by rw [e]; ring
    _ ≤ max (12 * Fm.CTu) 0 * (Fm.L x i).B0 := mul_le_mul_of_nonneg_right (le_max_left _ _) hB

end GlobalTheory.LevelBudget
