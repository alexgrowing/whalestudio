import Formalism.GaloisCohomology.StatementAlg

namespace Formalism.GaloisCohomology

theorem devTorsion : DevTorsion := by
  rintro R _ A B C _ _ _ _ _ _ f g ϖ c' c'' hex hker hA hC b ⟨k, hk⟩
  have hgb : ϖ ^ c'' • g b = 0 := hC _ ⟨k, by rw [← map_smul, hk, map_zero]⟩
  obtain ⟨a, ha⟩ : ϖ ^ c'' • b ∈ Set.range f := (hex _).1 (by rw [map_smul]; exact hgb)
  have hfa : f (ϖ ^ k • a) = 0 := by
    rw [map_smul, ha, smul_smul, mul_comm, ← smul_smul, hk, smul_zero]
  obtain ⟨j, hj⟩ := hker _ hfa
  have ha0 : ϖ ^ c' • a = 0 := hA a ⟨j + k, by rw [pow_add, mul_smul, hj]⟩
  rw [pow_add, mul_smul, ← ha, ← map_smul, ha0, map_zero]

end Formalism.GaloisCohomology
