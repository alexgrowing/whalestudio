import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalRep

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

theorem highest_weight_dominant_pair {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) {a b : Fin n} (hab : a < b) : lam b ≤ lam a := by
  have hne : a ≠ b := ne_of_lt hab
  have hw := (mem_weightSpace_iff_diagonal_rep E lam v).1 hv.2.1
  have hhv : (E a a - E b b) v = ((lam a - lam b : ℤ) : K) • v := by
    rw [LinearMap.sub_apply, hw a, hw b, ← sub_smul]; push_cast; rfl
  by_cases h0 : E a a - E b b = 0
  · rw [h0, LinearMap.zero_apply] at hhv
    have := (smul_eq_zero.1 hhv.symm).resolve_right hv.1
    have h1 : lam a - lam b = 0 := by exact_mod_cast this
    omega
  have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) := by
    refine ⟨h0, ?_, ?_, ?_⟩
    · rw [Ring.lie_def, hE.1 a b b a]; simp
    · rw [sub_lie, Ring.lie_def, Ring.lie_def, hE.1 a a a b, hE.1 b b a b]
      simp [hne, hne.symm, two_smul]
    · rw [sub_lie, Ring.lie_def, Ring.lie_def, hE.1 a a b a, hE.1 b b b a]
      simp [hne, hne.symm, two_smul]
      abel
  have P : t.HasPrimitiveVectorWith v (((lam a - lam b : ℤ) : K)) :=
    ⟨hv.1, hhv, hv.2.2 a b hab⟩
  obtain ⟨m, hm⟩ := P.exists_nat
  have : lam a - lam b = (m : ℤ) := by exact_mod_cast hm
  omega

theorem highest_weight_dominant_holds : HighestWeightDominant := by
  intro K V _ _ _ _ _ n E hE lam v hv a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · exact highest_weight_dominant_pair hE hv h

end Formalism.MainNotions.G.GLWeightTheory
