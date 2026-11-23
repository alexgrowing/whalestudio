import Mathlib
import Formalism.LocalToGlobal.ExponentGrids.IntegerShiftClosedExponent
import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.ArithmeticBoundCyclicTwo
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols SPer IndefNum IndefCore)
open Formalism.L2.GlobalTheoryTheory (Arith.Cst Arith.Lev Arith.Lev.admitted Arith.sg Arith.elt Arith.eltBar Arith.pOf Arith.EatT)

noncomputable section

namespace Formalism.AtG

namespace UnitPeriodBounds

open PlacesLyingOver Formalism.DivisionValues.PlaceSumConjugation

variable {K : Type} [Field K] [NumberField K]

theorem perBd_mono [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {u : Dc.Mem}
    {Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)} {t : Bs.Tup} {w : HeightOneSpectrum (𝓞 K)} {s s' : ℝ}
    (h : s' ≤ s) (H : PerBd Dc u Nu t w s) : PerBd Dc u Nu t w s' := by
  intro φ hφ F hF
  rcases H φ hφ F hF with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (le_trans h h1)

end UnitPeriodBounds

open PlacesLyingOver UnitPeriodBounds Formalism.DivisionValues.PlaceSumConjugation Formalism.DivisionValues.ValuationRepresentative

theorem root_of_unity_valuation_zero : RootOfUnityIsUnit := by
  intro K _ _ c n hn hc w
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hc
    exact zero_ne_one hc
  have h := vw_pow' w c hc0 n
  rw [hc, vw_one'] at h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  rcases mul_eq_zero.mp h.symm with h1 | h1
  · exact absurd h1 hn'
  · exact h1

end Formalism.AtG
