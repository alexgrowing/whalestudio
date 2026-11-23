import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGamma1OfIsCuspFormCoeffSeqStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

open Matrix.SpecialLinearGroup
open scoped Pointwise

theorem norm_petersson_self_eq (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    ‖UpperHalfPlane.petersson (k : ℤ) f f z‖ = ‖f z‖ ^ 2 * z.im ^ k := by
  simp only [UpperHalfPlane.petersson, norm_mul, Complex.norm_conj, zpow_natCast, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg z.im_pos.le]
  ring

theorem cusp_decay : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (γ : SL(2, ℤ)), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) a → ∃ C δ : ℝ, 0 < δ ∧ ∀ τ : ℍ, 1 / 2 ≤ τ.im →
      ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k ≤ C * Real.exp (-δ * τ.im) := by
  intro k L N ε a γ hk hL hN hcf
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_cuspForm_gamma1_of_isCuspFormCoeffSeq k L N ε a hk hL hN hcf
  obtain ⟨C₀, hC₀⟩ := hcf.2
  haveI : NeZero L := ⟨hL.ne'⟩
  have : ((ConjAct.toConjAct (γ : GL (Fin 2) ℝ)⁻¹) • (Gamma1 L : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Gamma1 L : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ γ)⁻¹
  obtain ⟨δ, hδ, hd⟩ := (CuspFormClass.zero_at_infty (CuspForm.translate f γ)).petersson_exp_decay_left (k : ℤ) _
      (CuspForm.translate f γ)
  obtain ⟨D, hD, h⟩ := hd.exists_pos
  rw [Asymptotics.IsBigOWith, atImInfty, eventually_comap, eventually_atTop] at h
  obtain ⟨y, hy⟩ := h
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) (hC₀ UpperHalfPlane.I)
  refine ⟨max D (C₀ * Real.exp (δ * |y|)), δ, hδ, fun τ hτ => ?_⟩
  have key : ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k =
      ‖UpperHalfPlane.petersson (k : ℤ) (CuspForm.translate f γ) (CuspForm.translate f γ) τ‖ := by
    rw [show ((CuspForm.translate f γ : CuspForm _ _) : ℍ → ℂ) = (⇑f) ∣[(k : ℤ)] γ from rfl,
      UpperHalfPlane.petersson_slash_SL, norm_petersson_self_eq, hf]
  rw [key]
  rcases le_total y τ.im with h1 | h1
  · have h2 := hy _ h1 τ rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    exact h2.trans (by gcongr; exact le_max_left _ _)
  · rw [← key]
    have h3 : 1 ≤ Real.exp (δ * |y|) * Real.exp (-δ * τ.im) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith [le_abs_self y]
    calc ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k ≤ C₀ := hC₀ _
      _ ≤ C₀ * (Real.exp (δ * |y|) * Real.exp (-δ * τ.im)) := le_mul_of_one_le_right hC₀0 h3
      _ = C₀ * Real.exp (δ * |y|) * Real.exp (-δ * τ.im) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end GlobalTheory.EisM
