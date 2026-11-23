import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviNormInj

open GlobalTheory.MixModel

theorem phase_eq (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y' : Mx D r W.rank) (u : Mx D W.rank r) :
    GlobalTheory.LeviNorm.phase ψ W (adj (incA D D.host.xi0⁻¹ • (HMul.hMul y' (giA W)))) u =
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y' : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) := by
  rw [GlobalTheory.LeviNorm.phase_apply, adj_adj]
  congr 2
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul, Matrix.mul_assoc, giA_gA_cancel]

theorem eq_of_phase_integral_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ N₁ N₂ : Mx D W.rank r → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ μ → Integrable N₂ μ → (∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₁ u ∂μ = ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₂ u ∂μ) → N₁ = N₂ := by
  intro D ψ hψ W r μ hμ N₁ N₂ hc₁ hc₂ hi₁ hi₂ h
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D W.rank r
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hcont : ∀ y : Mx D r W.rank, Continuous fun u : Mx D W.rank r =>
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) :=
    fun y => hψ.1.1.comp (ht.comp (continuous_finset_sum _ fun i _ =>
      ((continuous_const.matrix_mul continuous_id).matrix_elem i i)))
  have hint : ∀ (y : Mx D r W.rank) (N : Mx D W.rank r → ℂ), Integrable N μ → Integrable (fun u =>
      ψ (Algebra.trace (AF D.host.F) (AE D) (Matrix.trace (HMul.hMul (y : Matrix (Fin r) (Fin W.rank) (AE D)) (u : Matrix (Fin W.rank) (Fin r) (AE D))))) * N u) μ := by
    intro y N hN
    have := hN.mul_bdd (hcont y).aestronglyMeasurable (c := 1) (Filter.Eventually.of_forall fun u => (hψ.1.2.1 _).le)
    simpa only [mul_comm] using this
  rw [← sub_eq_zero]
  refine GlobalTheory.AdelicMatFourier.eq_zero_of_fourier_eq_zero D ψ hψ W.rank r μ hμ (N₁ - N₂) (hc₁.sub hc₂) (hi₁.sub hi₂) fun y' => ?_
  have e := h (adj (incA D D.host.xi0⁻¹ • (HMul.hMul y' (giA W))))
  simp only [phase_eq] at e
  simp only [Pi.sub_apply, mul_sub]
  rw [integral_sub (hint y' N₁ hi₁) (hint y' N₂ hi₂), e, sub_self]

end GlobalTheory.LeviNormInj
