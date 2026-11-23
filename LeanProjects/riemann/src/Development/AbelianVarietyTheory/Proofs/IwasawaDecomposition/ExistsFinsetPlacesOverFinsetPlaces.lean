import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.PlacesOver

theorem finite_fibre (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) :
    {w : HeightOneSpectrum (𝓞 K) | w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal}.Finite := by
  have hne : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot v.ne_bot
  refine (Ideal.finite_factors hne).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, hw]

theorem places_over_finset (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ T ↔ ∃ v ∈ S,
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  have hfin : (⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 K) |
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal}).Finite :=
    S.finite_toSet.biUnion fun v _ => finite_fibre E K v
  refine ⟨hfin.toFinset, fun w => ?_⟩
  simp

end GlobalTheory.PlacesOver
