import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

theorem isEulerProd_const_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0)
    (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) :
    IsEulerProd b I c minf m ↔ IsEulerProd b I 1 (c • minf) m := by
  constructor
  · rintro ⟨h1, h2, S₀, h3⟩
    refine ⟨h1, h2, S₀, fun S hS φinf φ hφi hφ => ?_⟩
    rw [h3 S hS φinf φ hφi hφ, lintegral_smul_measure, ENNReal.smul_def]
    simp only [ENNReal.coe_one, one_mul, smul_eq_mul]
    ring
  · rintro ⟨h1, h2, S₀, h3⟩
    refine ⟨h1, h2, S₀, fun S hS φinf φ hφi hφ => ?_⟩
    rw [h3 S hS φinf φ hφi hφ, lintegral_smul_measure, ENNReal.smul_def]
    simp only [ENNReal.coe_one, one_mul, smul_eq_mul]
    ring

end PositivityTheory.SiegelWeilFormula.Densx

end
