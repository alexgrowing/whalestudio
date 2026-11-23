import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceBound
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceUmg

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} {n r s : ℕ}

private theorem bnd : ∀ {n : ℕ} (d : Dat S n) (N : ℕ), ∃ C R : ℝ, ∀ (φ : Sm E n) (B : ℝ), Umg φ →
    (∀ g, ‖φ.1 g‖ ≤ B * AutomorphicForm.height g ^ N) → ∀ t, ‖d.comp φ.1 t‖ ≤ C * B * Real.exp (R * ‖t‖) := by
  intro n d N
  induction d with
  | nil => exact ⟨AutomorphicForm.height (1 : GA E 0) ^ N, 0, fun φ B _ h t => by
      rw [zero_mul, Real.exp_zero, mul_one, mul_comm]; exact h 1⟩
  | @cons r s b d ih =>
    obtain ⟨C, R, h1⟩ := (sliceBound E S r s b).1 N
    obtain ⟨C', R', h2⟩ := ih
    refine ⟨|C' * C|, |R| + |R'|, fun φ B hφ hB (t : Fin (d.len + 1) → ℝ) => ?_⟩
    obtain ⟨ψ, e, hψ, -⟩ := sliceUmg E S r s b (t 0) φ hφ
    have h3 := h2 ψ (C * B * Real.exp (R * |t 0|)) hψ (fun m => e ▸ h1 φ B hφ hB (t 0) m) fun j => t j.succ
    rw [e] at h3
    refine le_trans h3 ?_
    have hB0 : 0 ≤ B := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hB 1)) (pow_pos (AutomorphicForm.height_pos _) N)
    have a1 : |t 0| ≤ ‖t‖ := norm_le_pi_norm t 0
    have a2 : ‖fun j : Fin d.len => t j.succ‖ ≤ ‖t‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm t j.succ
    have a3 : Real.exp (R * |t 0|) * Real.exp (R' * ‖fun j : Fin d.len => t j.succ‖) ≤ Real.exp ((|R| + |R'|) * ‖t‖) := by
      rw [← Real.exp_add, add_mul]
      exact Real.exp_le_exp.2 (add_le_add (mul_le_mul (le_abs_self R) a1 (abs_nonneg _) (abs_nonneg _))
        (mul_le_mul (le_abs_self R') a2 (norm_nonneg _) (abs_nonneg _)))
    calc _ = C' * C * B * (Real.exp (R * |t 0|) * Real.exp (R' * ‖fun j : Fin d.len => t j.succ‖)) := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hB0) a3 (by positivity) (by positivity)

private theorem lin : ∀ {n : ℕ} (d : Dat S n) (φ ψ : Sm E n) (c : ℂ), Umg φ → Umg ψ →
    ∀ t, d.comp (c • φ + ψ).1 t = c * d.comp φ.1 t + d.comp ψ.1 t := by
  intro n d
  induction d with
  | nil => exact fun φ ψ c _ _ t => rfl
  | @cons r s b d ih =>
    intro φ ψ c hφ hψ (t : Fin (d.len + 1) → ℝ)
    obtain ⟨φ', e, hφ', -⟩ := sliceUmg E S r s b (t 0) φ hφ
    obtain ⟨ψ', e', hψ', -⟩ := sliceUmg E S r s b (t 0) ψ hψ
    have h := ih φ' ψ' c hφ' hψ' fun j => t j.succ
    have e2 : (c • φ' + ψ').1 = slice b.f.1 (t 0) (c • φ + ψ).1 := funext fun m => by
      rw [(sliceBound E S r s b).2 φ ψ c hφ hψ, ← e, ← e']; rfl
    rw [e2, e, e'] at h
    exact h

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.compBound :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CompBound E :=
  fun _ _ _ _ _ _ d => ⟨UpperTheory.ConvolutionTheory.BW.bnd d, UpperTheory.ConvolutionTheory.BW.lin d⟩
