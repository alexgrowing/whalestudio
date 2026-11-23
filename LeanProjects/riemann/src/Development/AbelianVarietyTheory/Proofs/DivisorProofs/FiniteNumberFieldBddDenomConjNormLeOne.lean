import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NumFin

theorem finite_bdd_denom_conj_le_one : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ), 0 < d → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1}.Finite := by
  intro E _ _ d hd
  have hd0 : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  set S := {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} with hS
  have hF := NumberField.Embeddings.finite_of_norm_le E ℂ (d : ℝ)
  have himg : (fun z : E => (d : E) * z) '' S ⊆ {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ)} := by
    rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
    refine ⟨?_, fun φ => ?_⟩
    · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((d : E) * z) fun w => by
        have h := hz1 w
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        convert h using 2
        rw [← map_natCast (algebraMap E (w.adicCompletion E)) d, ← map_mul]
        rfl
      show IsIntegral ℤ ((d : E) * z)
      rw [← hr]
      exact RingOfIntegers.isIntegral_coe r
    · rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      calc (d : ℝ) * ‖φ z‖ ≤ (d : ℝ) * 1 := by gcongr; exact hz2 φ
        _ = d := mul_one _
  have hinj : Set.InjOn (fun z : E => (d : E) * z) S := fun a _ b _ h => mul_left_cancel₀ hd0 h
  exact Set.Finite.of_finite_image (hF.subset himg) hinj

end GlobalTheory.NumFin
