import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowMulMemColonIdealFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMemA
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_pow_mul_mem_colonIdeal_frobenius : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂) (τ : ZMod a), ∀ α ∈ colon O K (F.mat τ), (X ^ e + (l : O⟦X⟧)) ^ (H + η) * α ∈ colon O K ((F.mat (τ - 1)).map (frob K l)) := by
  first | exact @GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob | exact GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob | (intros; apply GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob <;> assumption)
