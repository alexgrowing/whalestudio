import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem tendsto_pow_zero_of_valuation {K : Type} [Field K] [NumberField K] (v : P K) (y : Kv v)
    (hy : Valued.v y < 1) : Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero (Kv v) _).tendsto_right_iff]
  intro γ _
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hy (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := .ofClass (Valued.v : Valuation (Kv v) _))) γ)
  filter_upwards [eventually_ge_atTop n] with m hm
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hy.le hm) hn

private theorem valuation_lt_one_of_tendsto {K : Type} [Field K] [NumberField K] (v : P K) (y : Kv v)
    (hy : Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0)) : Valued.v y < 1 := by
  have h1 := (Valued.hasBasis_nhds_zero (Kv v) _).mem_of_mem (i := 1) trivial
  obtain ⟨n, hn⟩ := (hy.eventually h1 |>.and (eventually_gt_atTop 0)).exists
  obtain ⟨hn1, hn0⟩ := hn
  simp only [Set.mem_setOf_eq, Units.val_one, Valuation.restrict_lt_one_iff] at hn1
  rw [map_pow] at hn1
  by_contra hc
  exact absurd hn1 (not_lt.mpr (one_le_pow₀ (not_lt.mp hc)))

theorem UpperTheory.ConvolutionTheory.R2.I.below :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : P K) (w : P L) (i : Kv v →+* Kv w),
      Continuous i → (∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → Below v w := by
  intro K L _ _ _ _ _ v w i hi hx
  have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) := by
    intro x hxv
    rw [Ideal.mem_comap]
    have h1 : Valued.v (algebraMap K (Kv v) (x : K)) < 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) x).mpr hxv
      rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    have h2 := tendsto_pow_zero_of_valuation v _ h1
    have h3 : Tendsto (fun n : ℕ => (i (algebraMap K (Kv v) (x : K))) ^ n) atTop (𝓝 0) := by
      have := (hi.tendsto 0).comp h2
      simpa [Function.comp_def, map_pow] using this
    have h4 := valuation_lt_one_of_tendsto w _ h3
    rw [hx] at h4
    have h5 : algebraMap K L (x : K) = ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) := rfl
    rw [h5] at h4
    apply (w.valuation_lt_one_iff_mem (K := L) _).mp
    rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) hle
