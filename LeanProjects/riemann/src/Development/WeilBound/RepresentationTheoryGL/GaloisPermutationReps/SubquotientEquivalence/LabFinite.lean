import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

theorem lab_finite (K : Type) [Field K] [Finite K] (n : ℕ) : (Lab K n).Finite := by
  have h : Finite (Polynomial.degreeLT K (n + 1)) :=
    Finite.of_equiv _ (Polynomial.degreeLTEquiv K (n + 1)).symm.toEquiv
  refine Set.Finite.subset (Set.toFinite ((Polynomial.degreeLT K (n + 1) : Submodule K K[X]) : Set K[X])) fun P hP => ?_
  refine Polynomial.mem_degreeLT.2 (lt_of_le_of_lt Polynomial.degree_le_natDegree ?_)
  rw [hP.2.2.2]
  exact_mod_cast Nat.lt_succ_self n

end PositivityTheory.Rg.DzCount

end
