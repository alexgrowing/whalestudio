import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Etale

open IsLocalRing

noncomputable def jacobianMinor {R : Type*} [CommRing R] {m n : ℕ}
    (g : Fin m → MvPolynomial (Fin n) R) (ι : Fin m → Fin n) : MvPolynomial (Fin n) R :=
  (Matrix.of fun i j ↦ MvPolynomial.pderiv (ι j) (g i)).det

structure IsAdicCompletionMap {A : Type*} [CommRing A] [IsLocalRing A] {C : Type*} [CommRing C]
    (φ : A →+* C) : Prop where
  isAdicComplete : IsAdicComplete ((maximalIdeal A).map φ) C
  bijective : ∀ n : ℕ, Function.Bijective
    (Ideal.quotientMap ((maximalIdeal A ^ n).map φ) φ Ideal.le_comap_map)

end GroundTheory.Arith.Etale
