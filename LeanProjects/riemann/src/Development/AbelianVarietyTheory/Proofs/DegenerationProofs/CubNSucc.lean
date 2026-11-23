import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.CubeBalance

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem cubN_succ (θ : A → A → A → U) (k : ℕ) (x y : A) :
    cubN θ (k + 1) 1 x y = cubN θ k 1 x y * θ (x ^ k) x y := by
  simp only [cubN, Finset.prod_range_succ, _root_.one_mul]

theorem cubN_add (h : IsCub θ) (a b : ℕ) (x y : A) :
    cubN θ (a + b) 1 x y = θ (x ^ a) (x ^ b) y * cubN θ a 1 x y * cubN θ b 1 x y := by
  have s := h.N_split b (x ^ a) x y
  have e : cubN θ (a + b) 1 x y = cubN θ a 1 x y * cubN θ b (x ^ a) x y := by
    simp only [cubN, Finset.prod_range_add, _root_.one_mul, pow_add]
  rw [e, s, ← _root_.mul_assoc, mul_comm (cubN θ a 1 x y)]

theorem cubN_mul (h : IsCub θ) (a b : ℕ) (x y : A) :
    cubN θ (a * b) 1 x y = cubN θ a 1 (x ^ b) y * cubN θ b 1 x y ^ a := by
  induction a with
  | zero => simp [cubN]
  | succ a ih =>
    rw [Nat.succ_mul, cubN_add h, ih, cubN_succ, ← pow_mul, mul_comm b a, pow_succ]
    ac_rfl

theorem cubN_swap (h : IsCub θ) (a b : ℕ) (x y : A) :
    cubN θ a 1 x (y ^ b) * cubN θ b 1 y x ^ a = cubN θ b 1 y (x ^ a) * cubN θ a 1 x y ^ b := by
  induction b with
  | zero =>
    rw [pow_zero, h.N_one]
    simp [cubN]
  | succ b ih =>
    have n := h.N_add a 1 x (y ^ b) y
    rw [h.face, _root_.mul_one, _root_.one_mul] at n
    have r : ∀ z : A, θ (y ^ b) y z = θ z (y ^ b) y := fun z => by rw [h.s12, h.s01]
    rw [cubN_succ, cubN_succ, r, r, pow_succ y, mul_pow, pow_succ, mul_comm (cubN θ b 1 y x ^ a),
      ← _root_.mul_assoc, n]
    calc θ (x ^ a) (y ^ b) y * cubN θ a 1 x (y ^ b) * cubN θ a 1 x y * cubN θ b 1 y x ^ a
        = θ (x ^ a) (y ^ b) y * cubN θ a 1 x y * (cubN θ a 1 x (y ^ b) * cubN θ b 1 y x ^ a) := by ac_rfl
      _ = _ := by rw [ih]; ac_rfl

theorem balance : ∀ (A U : Type) [CommGroup A] [CommGroup U] (θ : A → A → A → U), IsCub θ → ∀ (a b : ℕ) (x y : A), cubN θ (a * b) 1 x y = cubN θ a 1 (x ^ b) y * cubN θ b 1 x y ^ a ∧ cubN θ a 1 x (y ^ b) * cubN θ b 1 y x ^ a = cubN θ b 1 y (x ^ a) * cubN θ a 1 x y ^ b ∧ cubN θ (a + b) 1 x y = θ (x ^ a) (x ^ b) y * cubN θ a 1 x y * cubN θ b 1 x y :=
  fun _ _ _ _ _ h a b x y => ⟨cubN_mul h a b x y, cubN_swap h a b x y, cubN_add h a b x y⟩

end GlobalTheory.CubeBalance
