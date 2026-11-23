import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionEqUnitSmulOfDiagonalCoefficientEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem exists_scalar_of_forall_eigen {V : Type*} [AddCommGroup V] [Module ℂ V] (P : V → Prop)
    (hP : ∀ f g, P f → P g → P (f + g)) (M : Module.End ℂ V) (h : ∀ f, P f → ∃ c : ℂ, ‖c‖ = 1 ∧ M f = c • f) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, P f → M f = c • f := by
  by_cases h0 : ∃ f₀, P f₀ ∧ f₀ ≠ 0
  · obtain ⟨f₀, hf₀, hne⟩ := h0
    obtain ⟨c, hc, ec⟩ := h f₀ hf₀
    refine ⟨c, hc, fun f hf => ?_⟩
    by_cases ha : ∃ a : ℂ, f = a • f₀
    · obtain ⟨a, rfl⟩ := ha
      rw [LinearMap.map_smul, ec, smul_comm]
    · obtain ⟨e, -, ee⟩ := h f hf
      obtain ⟨d, -, ed⟩ := h (f + f₀) (hP _ _ hf hf₀)
      rw [LinearMap.map_add, ec, ee, smul_add] at ed
      have k : (e - d) • f = (d - c) • f₀ := by
        rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, ed, add_comm]
      have hed : e - d = 0 := by
        by_contra hn
        exact ha ⟨(e - d)⁻¹ * (d - c), by rw [mul_smul, ← k, smul_smul, inv_mul_cancel₀ hn, one_smul]⟩
      rw [hed, zero_smul] at k
      have hdc : d - c = 0 := (smul_eq_zero.1 k.symm).resolve_right hne
      rw [ee, sub_eq_zero.1 hed, sub_eq_zero.1 hdc]
  · refine ⟨1, norm_one, fun f hf => ?_⟩
    have : f = 0 := by
      by_contra hn
      exact h0 ⟨f, hf, hn⟩
    rw [this, LinearMap.map_zero, smul_zero]

theorem schur_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → M f = c • f := by
  intro D ψ hψ S T M hM hcomm hiso
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, -⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hc
  refine exists_scalar_of_forall_eigen _ (fun f g hf hg => GlobalTheory.OrientedHeis.theta_add hf hg) M fun f hf => ?_
  refine GlobalTheory.T.thetaFunction_eq_unitSmul_of_diagonalCoefficient_eq D ψ hψ S T μ 𝓕 hμ h𝓕 f (M f) hf (hM f hf) fun w => ?_
  rw [← hcomm w f hf]
  exact GlobalTheory.T.thetaFunction_scalarProduct_preserved_isometry D ψ hψ S T μ 𝓕 hμ h𝓕 M hM (hiso μ 𝓕 hμ h𝓕) _ _
    (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w) hf

end GlobalTheory.Mem.Lift
