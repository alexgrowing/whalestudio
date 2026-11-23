import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem tame_scale : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c c' : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (a : Qbar l), c.O ≤ c'.O → a ∈ c'.O → Tame c W y n w ψ → Tame c' W (fun s => a • y s) n w ψ := by
  intro l _ Ω _ _ _ W c c' y n w ψ a hle ha hT
  obtain ⟨Y, P, u, b, hY, hYO, hP, hu, hb, hco, hsum, hfr, htame⟩ := hT
  refine ⟨fun s x => a • Y s x, P, u, a • b, ?_, ?_, hle hP, hu, ?_, ?_, ?_, hfr, ?_⟩
  · exact hY.const_smul a
  · intro s x i
    simpa using c'.O.mul_mem ha (hle (hYO s x i))
  · intro i
    simpa using c'.O.mul_mem ha (hle (hb i))
  · intro s t x
    simp only [hco s t x, smul_add, Matrix.mulVec_smul]
  · intro s
    rw [finsum_eq_sum_of_fintype] at *
    rw [← Finset.smul_sum, ← finsum_eq_sum_of_fintype, hsum s]
    simp only [smul_add, smul_sub, Matrix.mulVec_smul, smul_comm a P]
  · intro q hq hl
    obtain ⟨B, hB, t, htO, ht⟩ := htame q hq hl
    refine ⟨B, hB, fun x => a • t x, ?_, ?_⟩
    · intro x i
      simpa using c'.O.mul_mem ha (hle (htO x i))
    · intro s hs x
      simp only [ht s hs x, smul_sub, Matrix.mulVec_smul]

end GlobalTheory.Ord2
