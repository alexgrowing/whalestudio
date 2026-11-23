import Mathlib
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.LocalRingCardinality.DataLevel
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory

theorem adicCompletion_mem_integers_of_isIntegral_int {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {y : v.adicCompletion F} (hy : IsIntegral ℤ y) :
    y ∈ v.adicCompletionIntegers F := by
  let O := v.adicCompletionIntegers F
  have hint : (Valued.v : Valuation (v.adicCompletion F) _).Integers O :=
    Valuation.integer.integers _
  have hy' : IsIntegral O y := hy.tower_top
  exact hint.mem_of_integral hy'

theorem splitting_fst_mem_integers : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
    (∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) →
    ∀ z ∈ Formalism.BasicNotions.intV E v, (spl z).1 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ v spl h1 z hz
  let φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp spl.toRingHom
  let ψ : E →+* v.adicCompletion F := φ.comp Algebra.TensorProduct.includeLeftRingHom
  have key : Formalism.BasicNotions.intV E v ≤ (v.adicCompletionIntegers F).toSubring.comap φ := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro w (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨r, rfl⟩ := hx
      show ψ (algebraMap (𝓞 E) E r) ∈ v.adicCompletionIntegers F
      apply adicCompletion_mem_integers_of_isIntegral_int
      obtain ⟨p, hm, hp⟩ : IsIntegral ℤ (algebraMap (𝓞 E) E r) := RingOfIntegers.isIntegral_coe r
      refine ⟨p, hm, ?_⟩
      have h2 := congrArg ψ hp
      rw [Polynomial.hom_eval₂, map_zero] at h2
      rw [Polynomial.eval₂_eq_sum_range] at h2 ⊢
      simpa using h2
    · show (spl ((1 : E) ⊗ₜ[F] y)).1 ∈ v.adicCompletionIntegers F
      rw [h1]
      exact hy
  exact key hz

end GlobalTheory
