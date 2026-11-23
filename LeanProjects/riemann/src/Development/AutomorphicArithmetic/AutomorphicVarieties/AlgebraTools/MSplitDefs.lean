import Mathlib

noncomputable section

open Polynomial

namespace UpperTheory.V.AlgebraTools

variable {R κ : Type} [CommRing R] (P : κ → R[X]) (n : ℕ)

def mSplitIdeal : Ideal (MvPolynomial (κ × Fin n) R) :=
  Ideal.span (Set.range fun jk : κ × ℕ =>
    (∏ i : Fin n, (X - C (MvPolynomial.X (jk.1, i) : MvPolynomial (κ × Fin n) R)) -
      (P jk.1).map MvPolynomial.C).coeff jk.2)

abbrev MSplitAlg : Type := MvPolynomial (κ × Fin n) R ⧸ mSplitIdeal P n

def MSplitAlg.root (j : κ) (i : Fin n) : MSplitAlg P n := Ideal.Quotient.mk _ (MvPolynomial.X (j, i))

theorem MSplitAlg.prod_root (j : κ) :
    ∏ i : Fin n, (X - C (MSplitAlg.root P n j i)) = (P j).map (algebraMap R (MSplitAlg P n)) := by
  have h : (∏ i : Fin n, (X - C (MvPolynomial.X (j, i) : MvPolynomial (κ × Fin n) R)) -
      (P j).map MvPolynomial.C).map (Ideal.Quotient.mk (mSplitIdeal P n)) = 0 := by
    ext k
    rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨(j, k), rfl⟩
  rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero] at h
  simp only [Polynomial.map_sub, map_X, map_C] at h
  exact h

def MSplitAlg.lift {A : Type} [CommRing A] [Algebra R A] (a : κ → Fin n → A)
    (h : ∀ j, ∏ i : Fin n, (X - C (a j i)) = (P j).map (algebraMap R A)) : MSplitAlg P n →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2) fun x hx => by
    refine (Ideal.span_le (I := RingHom.ker
      (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 : MvPolynomial (κ × Fin n) R →ₐ[R] A))).2 ?_ hx
    rintro _ ⟨⟨j, k⟩, rfl⟩
    have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X (j, i) : MvPolynomial (κ × Fin n) R)) -
        (P j).map MvPolynomial.C).map
        (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 : MvPolynomial (κ × Fin n) R →ₐ[R] A).toRingHom = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero]
      have h3 : (MvPolynomial.aeval fun p : κ × Fin n => a p.1 p.2 :
          MvPolynomial (κ × Fin n) R →ₐ[R] A).toRingHom.comp MvPolynomial.C = algebraMap R A :=
        RingHom.ext fun r => by simp
      rw [h3, ← h j]
      simp
    have h4 := congrArg (fun q => q.coeff k) h2
    simp only [coeff_map, coeff_zero] at h4
    exact h4

theorem MSplitAlg.lift_root {A : Type} [CommRing A] [Algebra R A] (a : κ → Fin n → A)
    (h : ∀ j, ∏ i : Fin n, (X - C (a j i)) = (P j).map (algebraMap R A)) (j : κ) (i : Fin n) :
    MSplitAlg.lift P n a h (MSplitAlg.root P n j i) = a j i :=
  MvPolynomial.aeval_X (fun p : κ × Fin n => a p.1 p.2) (j, i)

theorem MSplitAlg.hom_ext {A : Type} [CommRing A] [Algebra R A] {f g : MSplitAlg P n →ₐ[R] A}
    (h : ∀ j i, f (MSplitAlg.root P n j i) = g (MSplitAlg.root P n j i)) : f = g :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun p => h p.1 p.2)

end UpperTheory.V.AlgebraTools
