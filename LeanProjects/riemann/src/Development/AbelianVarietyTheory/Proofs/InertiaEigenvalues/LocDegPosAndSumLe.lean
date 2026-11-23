import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDegreeSum
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.Proof.LocDegPos

theorem locDeg_pos_and_sum_le : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), l.Prime → (∀ v : HeightOneSpectrum (𝓞 E), 0 < Formalism.MainNotions.N.locDeg E v) ∧ ∀ s : Finset (HeightOneSpectrum (𝓞 E)), (∀ v ∈ s, v ∈ placesOver E l) → ∑ v ∈ s, Formalism.MainNotions.N.locDeg E v ≤ Module.finrank ℚ E := by
  intro E _ _ l hl
  refine ⟨fun v => ?_, fun s hs => ?_⟩
  · haveI := v.isPrime
    exact Nat.mul_pos (Ideal.ramificationIdx_pos v.asIdeal ℤ) (Ideal.inertiaDeg_pos v.asIdeal ℤ)
  · classical
    haveI : Fact l.Prime := ⟨hl⟩
    have hfin : Set.Finite {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal} := by
      have hf : ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)).Finite :=
        IsDedekindDomain.primesOver_finite _ _
      refine Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)
        (hf.subset ?_) (fun a _ b _ h => HeightOneSpectrum.ext h)
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨v.isPrime, ?_⟩
      rw [Ideal.liesOver_span_iff v.isPrime.ne_top (Nat.prime_iff_prime_int.1 hl)]
      simpa using hv
    letI : Fintype {v : HeightOneSpectrum (𝓞 E) // ((l : ℕ) : 𝓞 E) ∈ v.asIdeal} := hfin.fintype
    have hsum := GlobalTheory.Proof.LocalDegreeSum.sum_locDeg E l
    rw [← hsum, ← Finset.sum_subtype_of_mem (fun v => Formalism.MainNotions.N.locDeg E v) (p := fun v : HeightOneSpectrum (𝓞 E) => ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) (fun v hv => hs v hv)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end GlobalTheory.Proof.LocDegPos
