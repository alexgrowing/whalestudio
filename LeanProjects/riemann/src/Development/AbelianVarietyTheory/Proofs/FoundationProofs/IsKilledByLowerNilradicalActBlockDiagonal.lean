import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.KilledByLowerStable

theorem act_eq_zero_of_lower {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x : V) (hx : KilledByLower act x) (Y : Mat p q)
    (h1 : ∀ (a : Fin p) (j : Ix p q), Y (Sum.inl a) j = 0)
    (h2 : ∀ (i : Ix p q) (b : Fin q), Y i (Sum.inr b) = 0) : act Y x = 0 := by
  have hY : Y = ∑ i, ∑ j, Y i j • Eab i j := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Eab, Matrix.smul_single]
  rw [hY]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rcases i with a | b
  · rw [h1, zero_smul]
  · rcases j with a | b'
    · rw [hx a b, smul_zero]
    · rw [h2, zero_smul]

theorem killedByLower_act : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ Z : Mat p q, IsKC Z →
    ∀ x : V, KilledByLower act x → KilledByLower act (act Z x) := by
  intro p q V _ _ act hact Z hZ x hx a b
  have h := congrArg (fun f : Module.End ℂ V => f x) (hact (Eab (Sum.inr b) (Sum.inl a)) Z)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hx a b, map_zero, sub_zero] at h
  rw [← h]
  apply act_eq_zero_of_lower act x hx
  · intro a' j
    have h0 : Z (Sum.inl a') (Sum.inr b) = 0 := hZ _ _ (by simp [sameBlock])
    by_cases hj : j = Sum.inl a
    · subst hj
      simp [Eab, h0]
    · simp [Eab, hj]
  · intro i b'
    have h0 : Z (Sum.inl a) (Sum.inr b') = 0 := hZ _ _ (by simp [sameBlock])
    by_cases hi : i = Sum.inr b
    · subst hi
      simp [Eab, h0]
    · simp [Eab, hi]

end GlobalTheory.KilledByLowerStable
