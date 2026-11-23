import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.Uniformization
import GroundTheory.GlobalFields.ComplexMultiplication.UniformizationEisenstein

open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology
open scoped PeriodPair Real

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

def latticeOfTau (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    refine LinearIndependent.pair_iff.2 fun s t h ↦ ?_
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp at him hre
    have hs : s = 0 := by
      rcases him with h | h
      · exact h
      · exact absurd h τ.im_pos.ne'
    subst hs
    simp at hre
    exact ⟨rfl, hre⟩

@[simp] lemma latticeOfTau_ω₁ (τ : ℍ) : (latticeOfTau τ).ω₁ = τ := rfl
@[simp] lemma latticeOfTau_ω₂ (τ : ℍ) : (latticeOfTau τ).ω₂ = 1 := rfl

theorem G_latticeOfTau {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) :
    (latticeOfTau τ).G k = 2 * riemannZeta k * E hk τ := by
  have hE : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  have h1 : (latticeOfTau τ).G k = ∑' v : Fin 2 → ℤ, eisSummand k v τ := by
    rw [PeriodPair.G, ← (latticeOfTau τ).latticeEquivProd.symm.toEquiv.tsum_eq,
      ← (finTwoArrowEquiv ℤ).tsum_eq]
    refine tsum_congr fun v ↦ ?_
    simp only [LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply, finTwoArrowEquiv_apply,
      latticeOfTau_ω₁, latticeOfTau_ω₂, mul_one, eisSummand, zpow_neg, zpow_natCast]
    rfl
  rw [h1, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk, hE]
  ring

lemma riemannZeta_six : riemannZeta 6 = π ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  have hb : bernoulli 6 = 1 / 42 := by decide +kernel
  rw [hb] at h
  norm_num [Nat.factorial] at h
  rw [h]
  ring

theorem g₂_latticeOfTau (τ : ℍ) : (latticeOfTau τ).g₂ = 4 / 3 * π ^ 4 * E₄ τ := by
  rw [PeriodPair.g₂, G_latticeOfTau (k := 4) (by norm_num)]
  have : ((4 : ℕ) : ℂ) = 4 := by norm_num
  rw [this, riemannZeta_four]
  ring

theorem g₃_latticeOfTau (τ : ℍ) : (latticeOfTau τ).g₃ = 8 / 27 * π ^ 6 * E₆ τ := by
  rw [PeriodPair.g₃, G_latticeOfTau (k := 6) (by norm_num)]
  have : ((6 : ℕ) : ℂ) = 6 := by norm_num
  rw [this, riemannZeta_six]
  ring

def modularJ (τ : ℍ) : ℂ := E₄ τ ^ 3 / ModularForm.discriminant τ

theorem discr_latticeOfTau (τ : ℍ) :
    discr (latticeOfTau τ) = (2 * π) ^ 12 * ModularForm.discriminant τ := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [discr, g₂_latticeOfTau, g₃_latticeOfTau, h]
  ring

theorem weierstrassCurve_latticeOfTau_j (τ : ℍ) :
    (weierstrassCurve (latticeOfTau τ)).j = modularJ τ := by
  have hΔ := ModularForm.discriminant_ne_zero τ
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [weierstrassCurve_j, discr_latticeOfTau, g₂_latticeOfTau, modularJ]
  field_simp
  ring

theorem modularJ_smul (γ : SL(2, ℤ)) (τ : ℍ) : modularJ (γ • τ) = modularJ τ := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' E₄ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  simp only [CuspForm.coe_discriminant] at hΔ
  have hd := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  have hΔ0 := ModularForm.discriminant_ne_zero τ
  rw [modularJ, modularJ, show γ • τ = (γ : GL (Fin 2) ℝ) • τ from rfl, h4, hΔ]
  have : (denom (γ : GL (Fin 2) ℝ) τ ^ (4 : ℤ)) ^ 3 = denom (γ : GL (Fin 2) ℝ) τ ^ (12 : ℤ) := by
    rw [← zpow_natCast, ← zpow_mul]; norm_num
  rw [mul_pow, this, mul_div_mul_left _ _ (zpow_ne_zero _ hd)]

end Elliptic
end GroundTheory.Global
