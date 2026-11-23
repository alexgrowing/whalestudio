import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WMove

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ x : Mx D T.rank ρ, (∀ h, d.mixS T ψ μ 𝓕 (om (1, h) f) x = d.mixS T ψ μ 𝓕 (om (1, h) (heisO ψ S T (d.extX T (mt T h⁻¹ ⬝ x)) f)) 0) ∧ (∀ a g, d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) x = d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) (heisO ψ S T (d.extX T (x ⬝ a.1)) f)) 0) ∧ ∀ n : GA D S, d.mixS T ψ μ 𝓕 (om (n, 1) f) x = d.mixS T ψ μ 𝓕 (om (n, 1) (heisO ψ S T (d.extX T x ⬝ mt S n) f)) 0 := by
  intro D ψ S S₀ T ρ d χS χT om hω μ 𝓕 hμ f hf x
  have hb := fun F y => ((GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d).2.2.2.2.2.2.1 μ 𝓕 F y)
  refine ⟨fun h => ?_, fun a g => ?_, fun n => ?_⟩
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.extX_apply, HypDec.extX_apply, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, mt_one, Matrix.one_mul, _root_.mul_inv_rev, ← map_inv d.levi, ← map_inv d.emb0, mt_mul,
      ← Matrix.mul_assoc, d.extX_apply T (x ⬝ a.1), Matrix.mul_assoc _ d.pX, d.wittDecomp_projX_anisotropicEmbedding, ← d.extX_apply T (x ⬝ a.1),
      d.extX_levi, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]

end GlobalTheory.WMove
