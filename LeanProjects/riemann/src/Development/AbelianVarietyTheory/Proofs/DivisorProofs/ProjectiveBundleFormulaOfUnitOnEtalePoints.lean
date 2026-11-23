import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def pbfMap (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (n i : ℤ)
    (a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))) : Ht q (pullback V (PGL.pr N)) n i :=
  ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i)

def PBF (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) : Prop :=
  ∀ n i : ℤ, Function.Bijective (pbfMap q V n i)

theorem projectiveBundleFormula_of_unitOnEtalePoints (h : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V) : D1 :=
  fun q _ _ _ V hq n i => h q V hq n i

end GlobalTheory.EtC

end
