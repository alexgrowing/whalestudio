import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.PlaceOver

open Filter Topology

theorem isOpen_valuation_lt_one {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) :
    IsOpen {z : P.adicCompletion F | Valued.v z < 1} := by
  have h := Valued.isOpen_ball (P.adicCompletion F) 1
  simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using h

theorem valuation_lt_one_of_continuous {F F' : Type} [Field F] [NumberField F] [Field F'] [NumberField F']
    {P : HeightOneSpectrum (𝓞 F)} {P' : HeightOneSpectrum (𝓞 F')}
    (i : P.adicCompletion F →+* P'.adicCompletion F') (hi : Continuous i)
    {x : P.adicCompletion F} (hx : Valued.v x < 1) : Valued.v (i x) < 1 := by
  have hU : {y : P'.adicCompletion F' | Valued.v y < 1} ∈ 𝓝 (i 0) := by
    rw [map_zero]
    exact (isOpen_valuation_lt_one P').mem_nhds (by simp)
  have hV := hi.continuousAt.preimage_mem_nhds hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hV
  have hγ0 : (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) ≠ 0 := by
    simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx (Units.mk0 _ hγ0)
  have hxn : x ^ n ∈ i ⁻¹' {y : P'.adicCompletion F' | Valued.v y < 1} := by
    apply hγ
    show Valued.v.restrict (x ^ n) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
    exact hn
  have h1 : Valued.v (i x) ^ n < 1 := by simpa [map_pow] using hxn
  by_contra h
  exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 h)))

end GlobalTheory.PlaceOver

namespace GlobalTheory.PlaceOver

theorem valued_algebraMap {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (P.adicCompletion F) k) = P.valuation F k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k

theorem comap_eq_of_continuous_iso : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i →
    (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) →
    w'.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal := by
  intro E E' _ _ _ _ _ w w' i hi hc
  have hle : w.asIdeal ≤ w'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) := by
    intro e he
    rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E')]
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) (e : E)) < 1 := by
      rw [valued_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w e).2 he
    have h2 := valuation_lt_one_of_continuous (i : w.adicCompletion E →+* w'.adicCompletion E') hi h1
    have h3 : (i : w.adicCompletion E →+* w'.adicCompletion E') (algebraMap E (w.adicCompletion E) (e : E)) =
        algebraMap E' (w'.adicCompletion E') (algebraMap E E' (e : E)) := hc _
    rw [h3, valued_algebraMap] at h2
    exact h2
  exact (w.isMaximal.eq_of_le (Ideal.comap_ne_top _ w'.isPrime.ne_top) hle).symm

end GlobalTheory.PlaceOver
