import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHom
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

theorem iotaF_props : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Function.Injective (iotaF G v) ∧ (∀ z x, Commute (iotaF G v z) x) ∧ Module.finrank (Qv v) (Qv v ⊗[ℚ] G.C) = G.n ^ 2 * Module.finrank (Qv v) (Qv v ⊗[ℚ] G.F) := by
  intro p _ G v
  haveI : IsSimpleRing G.C := G.simpleC
  haveI : Nontrivial G.C := inferInstance
  haveI : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C
  refine ⟨?_, ?_, ?_⟩
  · have hf : Function.Injective ((IsScalarTower.toAlgHom ℚ G.F G.C).toLinearMap) :=
      (algebraMap G.F G.C).injective
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := Qv v) _ hf
    exact this
  · intro z x
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact ha.add_left hb
    | tmul a f =>
      induction x using TensorProduct.induction_on with
      | zero => exact Commute.zero_right _
      | add c d hc hd => exact hc.add_right hd
      | tmul b c =>
        rw [iotaF_tmul]
        show (a ⊗ₜ[ℚ] algebraMap G.F G.C f) * (b ⊗ₜ[ℚ] c) = (b ⊗ₜ[ℚ] c) * (a ⊗ₜ[ℚ] algebraMap G.F G.C f)
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm a b,
          Algebra.commutes]
  · rw [Module.finrank_baseChange, Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C,
      G.rankC, mul_comm]

end GlobalTheory.OrbFinAf
