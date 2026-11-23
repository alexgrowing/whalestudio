import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.Proof.LocalDegreeSum

theorem sum_locDeg : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] [Fintype {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}], ∑ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, ReciprocityTheory.Gal.locDeg v.1 = Module.finrank ℚ F := by
  intro F _ _ l hl _
  classical

  set p : Ideal ℤ := Ideal.span {(l : ℤ)} with hp
  have hpmax : p.IsMaximal := Int.ideal_span_isMaximal_of_prime l
  have : p.IsPrime := hpmax.isPrime
  have hp0 : p ≠ 0 := by
    rw [hp, Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.out.ne_zero

  have key : ∀ v : HeightOneSpectrum (𝓞 F),
      ((l : ℕ) : 𝓞 F) ∈ v.asIdeal ↔ v.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 F)) p := by
    intro v
    rw [Ideal.dvd_iff_le, hp, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_iff_mem]
    simp

  let e := (Equiv.subtypeEquivRight key).trans (HeightOneSpectrum.equivPrimesOver (𝓞 F) hp0)
  rw [← NumberField.RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)]
  exact Fintype.sum_equiv e _ _ (fun v => by rfl)

end GlobalTheory.Proof.LocalDegreeSum
