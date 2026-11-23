import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericLuDecompositionUnique
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuFactorsGenerateSameField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgIndepOfSameAdjoin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsCompatibleLaws

open scoped Matrix

namespace ModelDimension

theorem generic_flag_transition_matrices : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (E₀ F : Type) [AddCommGroup E₀] [Module K E₀] [AddCommGroup F] [Module L F] (j : E₀ →+ F) (S : Type) [Finite S] (r : S → ℕ) (V : S → Submodule K E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ), GlobalTheory.CompanionTheory.Ar.IsGenericFlag (Ω := K) (Ω' := L) j V b d → ∀ (e : ∀ s, Fin (r s) → E₀), (∀ s l, e s l ∈ V s) → (∀ s, LinearIndependent L fun l => j (e s l)) → ∃ v Tm : ∀ s, Matrix (Fin (r s)) (Fin (r s)) L, (∀ s k, v s k k = 1) ∧ (∀ s l k, l < k → v s l k = 0) ∧ AlgebraicIndependent K (fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin K (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) L = d ∧ (∀ s i, b s i = ∑ m, Tm s i m • ∑ l, v s l m • j (e s l)) ∧ (∀ s i m, i < m → Tm s i m = 0) ∧ ∀ s i, Tm s i i ≠ 0 := by
  intro K L _ _ _ E₀ F _ _ _ _ j S _ r V b d hg e he hli
  have hj : ∀ (a : K) x, j (a • x) = algebraMap K L a • j x := by
    obtain ⟨_, _, -, h, -⟩ := hg
    exact h
  have hli₀ : ∀ s, LinearIndependent K (e s) := fun s => by
    refine Fintype.linearIndependent_iff.2 fun g hg0 k => ?_
    have h1 : ∑ l, algebraMap K L (g l) • j (e s l) = 0 := by
      have := congrArg j hg0
      rw [map_sum, map_zero] at this
      simpa only [hj] using this
    have h2 := Fintype.linearIndependent_iff.1 (hli s) _ h1 k
    exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h2
  obtain ⟨v, Tm, h1, h0, hi, hd, hb, hT0, hTd⟩ := GlobalTheory.CompanionTheory.Ar.Rec.ReadEx.lin_core j V b d hg e hli₀ he hli
  refine ⟨v, Tm, h1, h0, hi, ?_, hb, hT0, hTd⟩
  rw [← GlobalTheory.CompanionTheory.Ar.Rec.ReadEx.adjoin_all_eq_strict v h1 h0]
  exact hd

end ModelDimension
