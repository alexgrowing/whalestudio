import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_unit :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), D.IsCH → (∀ x, IsUnit x ↔ IsUnit (D.val x)) ∧ Algebra.IsIntegral A E := by
  intro n A E _ _ _ D hD
  have h0 : ∀ x : E, Polynomial.aeval x (D.chi x) = 0 := ((d_chS D A).2.2 hD).2
  refine ⟨fun x => ⟨fun h => h.map D.val, fun h => ?_⟩, ⟨fun x => ?_⟩⟩
  · have h1 : D.lam n x = D.val x := (d_chi D x).2.2.2.1
    rw [← h1, Det.lam, Nat.sub_self] at h
    have hc : IsUnit ((D.chi x).coeff 0) := isUnit_of_mul_isUnit_right h
    have h2 := h0 x
    rw [← Polynomial.X_mul_divX_add (D.chi x), map_add, map_mul, Polynomial.aeval_X,
      Polynomial.aeval_C] at h2
    have h3 : IsUnit (x * Polynomial.aeval x (D.chi x).divX) := by
      rw [eq_neg_of_add_eq_zero_left h2]
      exact (hc.map (algebraMap A E)).neg
    have h4 : Commute x (Polynomial.aeval x (D.chi x).divX) := by
      have := (Commute.all (X : A[X]) (D.chi x).divX).map (Polynomial.aeval x)
      rwa [Polynomial.aeval_X] at this
    exact (h4.isUnit_mul_iff.1 h3).1
  · exact ⟨D.chi x, (d_chi D x).2.2.2.2.1, h0 x⟩
