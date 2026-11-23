import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobQIterateSelf
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem tensorMap_id_iterate_eq_self {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : B →ₐ[R] B) (r : ℕ) (hf : ∀ b, (⇑f)^[r] b = b) (x : A ⊗[R] B) :
    (⇑(Algebra.TensorProduct.map (AlgHom.id R A) f))^[r] x = x := by
  set e := Algebra.TensorProduct.map (AlgHom.id R A) f
  have ht : ∀ k (a : A) (b : B), (⇑e)^[k] (a ⊗ₜ[R] b) = a ⊗ₜ[R] (⇑f)^[k] b := by
    intro k a b
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      simp [e]
  have hadd : ∀ k (x y : A ⊗[R] B), (⇑e)^[k] (x + y) = (⇑e)^[k] x + (⇑e)^[k] y := by
    intro k x y
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_add, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
  have hzero : ∀ k, (⇑e)^[k] (0 : A ⊗[R] B) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
  induction x using TensorProduct.induction_on with
  | zero => exact hzero r
  | tmul a b => rw [ht, hf]
  | add x y hx hy => rw [hadd, hx, hy]

theorem sigKQ_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ),
    0 < r → ∀ x : KQ p K r, (⇑(sigKQ p K r))^[r] x = x := by
  intro p _ K r hr x
  exact tensorMap_id_iterate_eq_self (A := K) (frobQ p r) r (frobQ_iterate_self p r hr) x

end GlobalTheory.LKRes

example : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r → ∀ x : KQ p K r, (⇑(sigKQ p K r))^[r] x = x := GlobalTheory.LKRes.sigKQ_iterate_self
