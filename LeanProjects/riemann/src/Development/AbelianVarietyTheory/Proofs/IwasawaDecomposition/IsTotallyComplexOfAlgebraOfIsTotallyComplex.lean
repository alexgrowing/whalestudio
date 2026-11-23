import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory

theorem isTotallyComplex_of_algebra (E K : Type) [Field E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsTotallyComplex E] : IsTotallyComplex K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  have h := InfinitePlace.IsReal.comap (algebraMap E K) hw
  exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _) h

example : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsTotallyComplex E], IsTotallyComplex K :=
  fun E K _ _ _ _ _ _ => isTotallyComplex_of_algebra E K

end GlobalTheory
