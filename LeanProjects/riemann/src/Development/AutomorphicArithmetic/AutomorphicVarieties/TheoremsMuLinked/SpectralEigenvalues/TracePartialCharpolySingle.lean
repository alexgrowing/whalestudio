import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem UpperTheory.V.Th.Sp.trace_partial_charpoly_single {T G : Type} [CommRing T] [Group G] (t : MonoidAlgebra T G →ₗ[T] T)
    (g ta : G) (a y : T) :
    t (MonoidAlgebra.single g a * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y)) =
      a * (t (MonoidAlgebra.single (g * ta) 1) - t (MonoidAlgebra.single g 1)) -
        y * (a * t (MonoidAlgebra.single g 1)) := by
  have h : ∀ (k : G) (b : T), t (MonoidAlgebra.single k b) = b * t (MonoidAlgebra.single k 1) := fun k b => by
    rw [← smul_eq_mul, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [mul_sub, mul_sub, mul_one, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one,
    map_sub, map_sub, h (g * ta) a, h g a, h g (a * y)]
  ring

theorem UpperTheory.V.Th.Sp.q2 :
    ∀ (O T G X : Type) [CommRing O] [CommRing T] [Algebra O T] [Group G] [AddCommGroup X] [Module O X] (n : ℕ) (D : GDet n T G) (x : T →ₐ[O] O) (del : T →ₗ[O] X) (ta : G) (y : T) (Q : MonoidAlgebra T G), 1 ≤ n → IsDer x del → x y = 0 → (∀ g, x (D.tr (MonoidAlgebra.single (g * ta) 1)) = x (D.tr (MonoidAlgebra.single g 1))) → x (D.tr (Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y))) = 0 ∧ del (D.tr (Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y))) = del (D.tr (MonoidAlgebra.mapRingHom G ((algebraMap O T).comp (x : T →+* O)) Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 0))) - x (D.tr Q) • del y := by
  intro O T G X _ _ _ _ _ _ n D x del ta y Q hn hd hy hta
  obtain ⟨t, ht⟩ := (UpperTheory.V.CA.d_tr D.toDet).1 hn
  have ht' : ∀ z, D.tr z = t z := fun z => by rw [ht, (UpperTheory.V.CA.d_toDet D z).2.2.1]
  simp only [ht'] at hta ⊢
  induction Q using MonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ =>
    simp only [map_add, add_mul, hP.1, hQ.1, hP.2, hQ.2, add_zero, true_and, add_smul]
    abel
  | single g a =>
    have h : t (MonoidAlgebra.single g a) = a * t (MonoidAlgebra.single g 1) := by
      rw [← smul_eq_mul, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [MonoidAlgebra.mapRingHom_single, UpperTheory.V.Th.Sp.trace_partial_charpoly_single, UpperTheory.V.Th.Sp.trace_partial_charpoly_single, h]
    have h0 : x (t (MonoidAlgebra.single (g * ta) 1) - t (MonoidAlgebra.single g 1)) = 0 := by
      rw [map_sub, hta, sub_self]
    refine ⟨by rw [map_sub, map_mul, map_mul, h0, hy, mul_zero, zero_mul, sub_zero], ?_⟩
    rw [map_sub, hd, hd, h0, hy, zero_smul, zero_smul, add_zero, zero_add, zero_mul, sub_zero, RingHom.comp_apply,
      ← Algebra.smul_def, map_smul]
    rfl
