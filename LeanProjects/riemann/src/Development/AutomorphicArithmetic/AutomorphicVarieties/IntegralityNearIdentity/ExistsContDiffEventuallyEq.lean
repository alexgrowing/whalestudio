import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.EqOneOfNear
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateOfRoots
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightedSumBis

open scoped ContDiff

namespace UpperTheory.V.Lib.Small

theorem conj_of_roots {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d) (N D : GL (Fin n) K)
    (hD : (D : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d)
    (hN : ∀ i, (N : Matrix (Fin n) (Fin n) K).charpoly.IsRoot (d i)) : ∃ g : GL (Fin n) K, N = g * D * g⁻¹ :=
  _root_.UpperTheory.Reformulated.B.ConjugateOfRoots.conj_of_roots d hd N D hD hN

theorem exists_eq_exp (f : ℝ → ℂ) (hc : Continuous f) (h0 : f 0 = 1) (hm : ∀ x y, f (x + y) = f x * f y) :
    ∃ c : ℂ, ∀ x : ℝ, f x = Complex.exp (c * x) :=
  _root_.UpperTheory.Reformulated.B.weightedSumBis.exists_eq_exp f hc h0 hm

end UpperTheory.V.Lib.Small
