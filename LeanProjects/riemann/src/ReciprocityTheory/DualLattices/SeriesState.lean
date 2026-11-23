import ReciprocityTheory.DualLattices.SqZeroOfSpan

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

def PairingPropertiesStatement (B : BX R₀) : Prop :=
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R), N • x = 0 → N • y = 0 → ∃ z, B.IsPairing N x y z) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x y z' → z = z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x x' y : B.G R) (z z' w : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x' y z' → B.IsPairing N (x + x') y w → w = z * z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y y' : B.G R) (z z' w : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x y' z' → B.IsPairing N x (y + y') w → w = z * z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N y x z' → z * z' = 1) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ), B.IsPairing N x y z → z ^ N = 1) ∧
  (∀ (R S : LAlg R₀) (f : LHom R S) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N (B.map f x) (B.map f y) (Units.map (f.1 : R →* S) z)) ∧
  (∀ (R : LAlg R₀) (N p : ℕ) (x y : B.G R) (z : (R : Type u)ˣ), N • x = 0 → (N * p) • y = 0 →
    B.IsPairing (N * p) x y z → B.IsPairing N x (p • y) z)

end ReciprocityTheory.PGsh
