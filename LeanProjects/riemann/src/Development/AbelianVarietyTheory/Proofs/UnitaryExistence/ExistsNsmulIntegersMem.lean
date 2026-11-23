import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

open IsDedekindDomain NumberField

namespace GlobalTheory.NsmulIntegersMembership

theorem valued_absNorm_lt_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) < 1 := by
  have h1 : v.valuation F (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) : F) < 1 :=
    (v.valuation_lt_one_iff_mem (K := F) _).2 (Ideal.absNorm_mem v.asIdeal)
  have h2 := v.valuedAdicCompletion_eq_valuation' (K := F) ((Ideal.absNorm v.asIdeal : ℕ) : F)
  have h3 : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((Ideal.absNorm v.asIdeal : ℕ) : F) := by
    rw [map_natCast]
  rw [h3]
  refine lt_of_eq_of_lt h2 ?_
  simpa using h1

end GlobalTheory.NsmulIntegersMembership
