import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlashStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorPolynomialGrowthQExpansionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem polyB_add_smul {u v : ℕ → ℂ} (c : ℂ) (hu : PolyB u) (hv : PolyB v) :
    PolyB (fun n => u n + c * v n) := by
  obtain ⟨C₁, A₁, h₁⟩ := hu
  obtain ⟨C₂, A₂, h₂⟩ := hv
  have hC₁ : 0 ≤ C₁ := by
    have := h₁ 0; simp at this; exact le_trans (norm_nonneg _) this
  have hC₂ : 0 ≤ C₂ := by
    have := h₂ 0; simp at this; exact le_trans (norm_nonneg _) this
  refine ⟨C₁ + ‖c‖ * C₂, A₁ + A₂, fun n => ?_⟩
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have e1 : ((n : ℝ) + 1) ^ A₁ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) := pow_le_pow_right₀ h1 (by omega)
  have e2 : ((n : ℝ) + 1) ^ A₂ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) := pow_le_pow_right₀ h1 (by omega)
  calc ‖u n + c * v n‖ ≤ ‖u n‖ + ‖c‖ * ‖v n‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ C₁ * ((n : ℝ) + 1) ^ A₁ + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ A₂) := by
        gcongr; exacts [h₁ n, h₂ n]
    _ ≤ C₁ * ((n : ℝ) + 1) ^ (A₁ + A₂) + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ (A₁ + A₂)) := by
        gcongr
    _ = (C₁ + ‖c‖ * C₂) * ((n : ℝ) + 1) ^ (A₁ + A₂) := by ring

theorem qs_To_hsum : ∀ (k q : ℕ) (ε : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → 0 < q → ε 1 = 1 → PolyB a →
    PolyB (To k (ε q) q a) ∧ qs (To k (ε q) q a) = hsum k ε (repT q) (qs a) := by
  intro k q ε a hk hq hε ha
  obtain ⟨hU, hUq⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k q a hk hq ha
  obtain ⟨hV, hVq⟩ := GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion q a hq ha
  have hTo : To k (ε q) q a = fun n => Uo q a n + (ε q * (q : ℂ) ^ (k - 1)) * Vo q a n := by
    funext n; simp only [To, Uo]
  refine ⟨by rw [hTo]; exact polyB_add_smul _ hU hV, ?_⟩
  funext τ
  have sU : Summable fun n : ℕ => Uo q a n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous _ hU).1 τ).of_norm
  have sV : Summable fun n : ℕ => Vo q a n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous _ hV).1 τ).of_norm
  have hsplit : qs (To k (ε q) q a) τ = qs (Uo q a) τ + (ε q * (q : ℂ) ^ (k - 1)) * qs (Vo q a) τ := by
    rw [hTo]; simp only [qs]
    rw [← tsum_mul_left, ← sU.tsum_add (sV.mul_left _)]
    congr 1; funext n; ring
  have him : 0 < ((q : ℂ) * (τ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hq) τ.im_pos
  have hσ : qs (Vo q a) τ = qs a ⟨(q : ℂ) * τ, him⟩ := hVq τ ⟨(q : ℂ) * τ, him⟩ rfl
  rw [hsplit, hUq τ, hσ, hsum, Fintype.sum_option]
  have hnone : ε (repT q none 0 0) * slz k (repT q none) (qs a) τ
      = (ε q * (q : ℂ) ^ (k - 1)) * qs a ⟨(q : ℂ) * τ, him⟩ := by
    have : ofComplex ((((q : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ))) = ⟨(q : ℂ) * τ, him⟩ := by
      rw [show (((q : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ)) = (q : ℂ) * τ by
        push_cast; ring]
      exact ofComplex_apply_of_im_pos him
    simp only [repT, slz, Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    rw [this]
    push_cast
    simp
    ring
  have hsome : ∀ j : Fin q, ε (repT q (some j) 0 0) * slz k (repT q (some j)) (qs a) τ
      = slz k (repU q j) (qs a) τ := by
    intro j
    simp only [repT, repU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hε, one_mul]
  rw [hnone, Finset.sum_congr rfl (fun j _ => hsome j)]
  ring

end GlobalTheory.EisM
