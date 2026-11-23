import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem IsPurePair.absSpace_eq_bot_of_finrank_le {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {q : ℝ} {f N : End ℂ V} (hp : IsPurePair q f N) (hN : IsNilpotent N)
    {i : ℤ} (hi : (finrank ℂ V : ℤ) ≤ |i|) : absSpace f (q ^ ((i : ℝ) / 2)) = ⊥ := by
  have h0 : N ^ finrank ℂ V = 0 := by
    have h1 := LinearMap.aeval_self_charpoly N
    rwa [hN.charpoly_eq_X_pow_finrank, map_pow, aeval_X] at h1
  have hk : ∀ k : ℕ, finrank ℂ V ≤ k → N ^ k = 0 := fun k hk => pow_eq_zero_of_le hk h0
  rw [eq_bot_iff]
  intro v hv
  rcases le_total 0 i with h | h
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have hv' : v ∈ absSpace f (q ^ ((k : ℝ) / 2)) := by simpa using hv
    obtain ⟨u, -, hu⟩ := (hp.2 k).2.2 hv'
    rw [hk k (by simpa using hi)] at hu
    simpa using hu.symm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
    have hv' : v ∈ absSpace f (q ^ (-(k : ℝ) / 2)) := by simpa using hv
    have := (hp.2 k).2.1 hv' (zero_mem _) (by simp [hk k (by simpa using hi)])
    simpa using this

end GlobalTheory.WeilDeligne
