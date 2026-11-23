import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem om_rat_mul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S T), IsWeilDatumO ψ S T χ χ' om → ∀ f, IsThetaFunO ψ S T f → ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ g h w, om (γ * g, γ' * h) f w = om (g, h) f (mt T γ'⁻¹ ⬝ w ⬝ mt S γ) := by
  intro D ψ S T χ χ' om H f hf γ hγ γ' hγ' g h w
  have h1 := GlobalTheory.WeilRat.om_rat_actO D ψ H.std S T χ χ' om H γ hγ γ' hγ' _ (H.om_pres (g, h) f hf)
    (mt T γ'⁻¹ ⬝ w ⬝ mt S γ)
  have h2 : actO S T γ γ' (mt T γ'⁻¹ ⬝ w ⬝ mt S γ) = w := by
    rw [actO_eq, Matrix.mul_assoc, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, mt_mul_inv,
      Matrix.one_mul]
  rw [h2] at h1
  rw [← h1, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]

end GlobalTheory.Unf
