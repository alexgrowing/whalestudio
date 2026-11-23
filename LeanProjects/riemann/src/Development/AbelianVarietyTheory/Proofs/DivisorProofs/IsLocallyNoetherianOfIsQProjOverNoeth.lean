import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isLocallyNoetherian_of_isQProjOver_noeth :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (f : X ⟶ Sp R),
      IsQProjOver f → IsLocallyNoetherian X := by
  intro R _ _ X f h
  obtain ⟨N, i, hi, -, e⟩ := h
  have : IsProper (PSpace.str R N) := isProper_str R N
  have : LocallyOfFiniteType f := by
    rw [← e]
    infer_instance
  have : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  exact LocallyOfFiniteType.isLocallyNoetherian f

end GlobalTheory
