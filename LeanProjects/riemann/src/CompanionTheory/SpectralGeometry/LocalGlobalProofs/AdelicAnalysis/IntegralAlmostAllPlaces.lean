import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodInt

theorem valued_algebraMap {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem eventually_le_one {F : Type} [Field F] [NumberField F] (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x ≤ 1 := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  rw [Filter.eventually_cofinite]
  refine h.subset fun v hv => ?_
  exact not_le.mp hv

theorem eventually_eq_one {F : Type} [Field F] [NumberField F] (x : F) (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x = 1 := by
  filter_upwards [eventually_le_one x, eventually_le_one x⁻¹] with v h1 h2
  refine le_antisymm h1 ?_
  rw [map_inv₀] at h2
  have h0 : v.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  exact (inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2

theorem repr_inclR {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R x) k = algebraMap F R (b.repr x k) := by
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] x) k = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem rational_integral_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ x : E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) x) k ∈ v.adicCompletionIntegers F) ∧ ∀ x : F, x ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) x) = 1 := by
  intro F E _ _ _ _ _ σ _ d b
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · have h : ∀ k : Fin d, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        v.valuation F (b.repr x k) ≤ 1 := fun k => eventually_le_one _
    filter_upwards [Filter.eventually_all.mpr h] with v hv k
    rw [repr_inclR, HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
    exact hv k
  · filter_upwards [eventually_eq_one x hx] with v hv
    rw [valued_algebraMap, hv]

end GlobalTheory.CompanionTheory.SW.GoodInt
