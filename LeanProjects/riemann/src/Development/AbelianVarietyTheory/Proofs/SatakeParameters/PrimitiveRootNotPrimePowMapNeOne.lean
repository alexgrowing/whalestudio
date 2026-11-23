import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory

theorem primitiveRoot_notPrimePow_map_ne_one :
    ∀ (k : Type) [Field k] (O : Type) [CommRing O] [IsDomain O] (f : O →+* k) (ζ : O) (n : ℕ),
      1 < n → IsPrimitiveRoot ζ n → (¬ IsPrimePow n) → f ζ ≠ 1 := by
  intro k _ O _ _ f ζ n hn hζ hpp h1
  have hroot : IsRoot (cyclotomic n O) ζ := hζ.isRoot_cyclotomic (by omega)
  have h0 : eval (f ζ) (cyclotomic n k) = 0 := by
    rw [← map_cyclotomic n f, eval_map, eval₂_at_apply, hroot.eq_zero, map_zero]
  have hone : eval (1 : k) (cyclotomic n k) = 1 := by
    apply eval_one_cyclotomic_not_prime_pow
    intro p hp j hj
    exact hpp (hj ▸ (Nat.Prime.isPrimePow hp).pow (by rintro rfl; simp at hj; omega))
  rw [h1, hone] at h0
  exact one_ne_zero h0

end GlobalTheory
