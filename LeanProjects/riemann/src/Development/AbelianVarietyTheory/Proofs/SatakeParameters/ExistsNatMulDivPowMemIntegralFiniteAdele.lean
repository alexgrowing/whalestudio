import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

set_option maxHeartbeats 800000

namespace GlobalTheory.DivInt
open GlobalTheory.AdeleBaseChange Formalism.UG.P

theorem exists_nat_mul_div_pow_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (w : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (∀ w', w' ≠ w → prV (E := E) w' z = 0) → ∀ (ℓ : ℕ), ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E := by
  intro F E _ _ _ _ _ w z hz ℓ hℓ
  obtain ⟨ι, hι⟩ := exists_toAd F E
  obtain ⟨x, r, hr, hzr⟩ := exists_approx z
  obtain ⟨D, hD, hDx⟩ := exists_nat_mul_integral ({x} : Finset E)
  obtain ⟨o, ho⟩ := hDx x (Finset.mem_singleton_self x)
  have hDz : algebraMap E _ (D : E) * ι z ∈ intAd E := by
    rw [hzr, map_add, map_tmul_one hι, mul_add, ← map_mul, ← nsmul_eq_mul, ← ho]
    exact add_mem (algebraMap_int_mem o) (mul_mem (by
      rw [← map_natCast (algebraMap (𝓞 E) E)]; exact algebraMap_int_mem _) (map_mem_int hι hr))
  refine ⟨D, hD, fun n => mem_int_of_map hι ?_⟩
  intro P
  rw [map_mul, map_tmul_one hι]
  change algebraMap E (P.adicCompletion E) ((D : E) / (ℓ : E) ^ n) * ι z P ∈ P.adicCompletionIntegers E
  by_cases hP : P.under (𝓞 F) = w
  · have hv : Valued.v (algebraMap E (P.adicCompletion E) (ℓ : E)) = 1 := by
      rw [levelaf_valued_algebraMap, ← map_natCast (algebraMap (𝓞 E) E),
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      intro hm
      apply hℓ
      rw [← hP, HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]
      exact hm
    have h1 := hDz P
    change algebraMap E (P.adicCompletion E) (D : E) * ι z P ∈ P.adicCompletionIntegers E at h1
    have e : algebraMap E (P.adicCompletion E) ((D : E) / (ℓ : E) ^ n) * ι z P =
        (algebraMap E (P.adicCompletion E) (ℓ : E))⁻¹ ^ n *
          (algebraMap E (P.adicCompletion E) (D : E) * ι z P) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, inv_pow]; ring
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
    rw [e, map_mul, map_pow, map_inv₀, hv, inv_one, one_pow, one_mul]
    exact h1
  · have h0 : ι z P = 0 := (prV_eq_zero_iff hι (P.under (𝓞 F)) z).1 (hz _ hP) P rfl
    rw [h0, mul_zero]
    exact zero_mem _

end GlobalTheory.DivInt
