import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
open NumberField IsDedekindDomain Formalism.L2.Ker

namespace GlobalTheory

theorem exists_not_mem_dvd_locally_away (E : Type) [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) (hr : r ≠ 0) :
    ∃ t : 𝓞 E, t ∉ Q.asIdeal ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), Q' ≠ Q →
      ∃ w : 𝓞 E, w ∉ Q'.asIdeal ∧ ∃ z : 𝓞 E, w * t = r * z := by
  have hI : Ideal.span {r} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hnu : ¬ IsUnit Q.asIdeal := fun h => Q.isPrime.ne_top (Ideal.isUnit_iff.1 h)
  obtain ⟨J, hJ, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hnu hI).exists_eq_pow_mul_and_not_dvd
  set m := multiplicity Q.asIdeal (Ideal.span {r})
  have hJle : ¬ J ≤ Q.asIdeal := fun h => hnd (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htJ, htQ⟩ := Set.not_subset.1 hJle
  refine ⟨t, htQ, fun Q' hQ' => ?_⟩
  have hnle : ¬ Q.asIdeal ^ m ≤ Q'.asIdeal := by
    intro h
    have h1 : Q.asIdeal ≤ Q'.asIdeal := Q'.isPrime.le_of_pow_le h
    have h2 : Q.asIdeal = Q'.asIdeal := Q.isMaximal.eq_of_le Q'.isPrime.ne_top h1
    exact hQ' (HeightOneSpectrum.ext h2.symm)
  obtain ⟨w, hwm, hwQ'⟩ := Set.not_subset.1 hnle
  refine ⟨w, hwQ', ?_⟩
  have hmem : w * t ∈ Ideal.span {r} := by
    rw [hJ]; exact Ideal.mul_mem_mul hwm htJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨z, by rw [← hz, mul_comm]⟩

end GlobalTheory
