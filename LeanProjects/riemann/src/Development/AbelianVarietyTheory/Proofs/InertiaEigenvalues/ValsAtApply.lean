import Mathlib

namespace GlobalTheory.UnitLemma

def valsAt {G : Type} [Group G] {ι : Type} (w : ι → G →* Multiplicative ℤ) {r : ℕ} (e : Fin r → ι) :
    G →* Multiplicative (Fin r → ℤ) where
  toFun x := Multiplicative.ofAdd fun j => Multiplicative.toAdd (w (e j) x)
  map_one' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    funext j
    simp
  map_mul' x y := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
    congr 1
    funext j
    simp

theorem valsAt_apply {G : Type} [Group G] {ι : Type} (w : ι → G →* Multiplicative ℤ) {r : ℕ}
    (e : Fin r → ι) (x : G) (j : Fin r) :
    Multiplicative.toAdd (valsAt w e x) j = Multiplicative.toAdd (w (e j) x) := rfl

end GlobalTheory.UnitLemma
