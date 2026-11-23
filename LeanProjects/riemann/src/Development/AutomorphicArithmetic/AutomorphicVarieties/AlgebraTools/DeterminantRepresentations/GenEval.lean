import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.genEval :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B] [Algebra A B] (m : ℕ) (y : Fin m → MonoidAlgebra A G) (b : Fin m → B),
    D.D B (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (y j)) =
      MvPolynomial.aeval b (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
  intro n A G _ _ D B _ _ m y b
  rw [← D.nat (MvPolynomial (Fin m) A) B (MvPolynomial.aeval b)]
  congr 1
  simp only [GDet.gen, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext g
  simp [MonoidAlgebra.mapRingHom]
