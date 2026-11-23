import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesSchwartzReal
open GlobalTheory.ArchSch

namespace GlobalTheory.QuadPhase

theorem hasTemperateGrowth_quadPhase : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : LinearMap.BilinForm ℝ V)
    (L : V →ₗ[ℝ] ℝ) (c : ℝ), Function.HasTemperateGrowth (fun x : V => ech (Q x x + L x + c)) := by
  intro V _ _ _ Q L c
  let B : V →L[ℝ] V →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ Q)
  let L' : V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap L
  have hB : ∀ x y, B x y = Q x y := fun _ _ => rfl
  have hL : ∀ x, L' x = L x := fun _ => rfl
  have hQ : Function.HasTemperateGrowth (fun x : V => B x x) :=
    B.bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id' Function.HasTemperateGrowth.id'
  have hP : Function.HasTemperateGrowth (fun x : V => B x x + L' x + c) :=
    (hQ.add L'.hasTemperateGrowth).add (Function.HasTemperateGrowth.const c)
  have h := GlobalTheory.SchOp.hasTemperateGrowth_ech.comp hP
  simpa only [Function.comp_def, hB, hL] using h

end GlobalTheory.QuadPhase
