import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorGeneratedLiftStatement

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfBC

def unitT (R : Type) [CommRing R] : (R[T;T⁻¹])ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; simp
  inv_val := by rw [← LaurentPolynomial.T_add]; simp

theorem bc_laur : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : A[T;T⁻¹] →ₐ[A] B) (f g : A), Pf p A → Pf p K → PQ p (i : A[T;T⁻¹] →+* B) (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → ∃ i₁ : K[T;T⁻¹] →+* B ⊗[A] K, PQ p i₁ (Ideal.span {LaurentPolynomial.C (algebraMap A K f) - LaurentPolynomial.T 1 * LaurentPolynomial.C (algebraMap A K g)}) ∧ (∀ a, i₁ (LaurentPolynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ ∀ n : ℤ, i₁ (LaurentPolynomial.T n) = i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K) := by
  intro p _ A _ B _ _ K _ _ i f g hA hK hPQ
  let j : A[T;T⁻¹] →+* K[T;T⁻¹] :=
    AddMonoidAlgebra.liftNCRingHom ((LaurentPolynomial.C : K →+* K[T;T⁻¹]).comp (algebraMap A K))
      (AddMonoidAlgebra.of K ℤ) (fun _ _ => Commute.all _ _)
  let i₁ : K[T;T⁻¹] →+* B ⊗[A] K :=
    AddMonoidAlgebra.liftNCRingHom
      (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom
      (((Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] K).comp
        (i : A[T;T⁻¹] →+* B)).toMonoidHom.comp (AddMonoidAlgebra.of A ℤ))
      (fun _ _ => Commute.all _ _)
  have hi1 : ∀ (n : ℤ) (k : K), i₁ (AddMonoidAlgebra.single n k) =
      ((1 : B) ⊗ₜ[A] k) * (i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K)) := by
    intro n k
    exact AddMonoidAlgebra.liftNC_single _ _ n k
  have hj1 : ∀ (n : ℤ) (a : A), j (AddMonoidAlgebra.single n a) =
      LaurentPolynomial.C (algebraMap A K a) * LaurentPolynomial.T n := by
    intro n a
    exact AddMonoidAlgebra.liftNC_single _ _ n a
  have hC : ∀ a, i₁ (LaurentPolynomial.C a) = (1 : B) ⊗ₜ[A] a := by
    intro a
    have h1 := hi1 0 a
    rw [LaurentPolynomial.T_zero, map_one, ← Algebra.TensorProduct.one_def, mul_one] at h1
    exact h1
  have hT : ∀ n : ℤ, i₁ (LaurentPolynomial.T n) = i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K) := by
    intro n
    have h1 := hi1 n 1
    rw [← Algebra.TensorProduct.one_def, one_mul] at h1
    exact h1
  have hjC : ∀ a, j (LaurentPolynomial.C a) = LaurentPolynomial.C (algebraMap A K a) := by
    intro a
    have h1 := hj1 0 a
    rw [LaurentPolynomial.T_zero, mul_one] at h1
    exact h1
  have hjT : ∀ n : ℤ, j (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
    intro n
    have h1 := hj1 n 1
    rw [map_one, map_one, one_mul] at h1
    exact h1
  have hiC : ∀ a, i (LaurentPolynomial.C a) = algebraMap A B a := by
    intro a
    rw [← AlgHom.commutes i a, LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self_apply]
  have hcomp : (LaurentPolynomial.C : K →+* K[T;T⁻¹]).comp (algebraMap A K) =
      j.comp (algebraMap A A[T;T⁻¹]) := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, LaurentPolynomial.algebraMap_apply,
      Algebra.algebraMap_self_apply, hjC]
  have hgen : Subring.closure (Set.range (LaurentPolynomial.C : K →+* K[T;T⁻¹]) ∪ Set.range j) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    refine LaurentPolynomial.induction_on' q ?_ ?_
    · intro a b ha hb
      exact Subring.add_mem _ ha hb
    · intro n a
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨a, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨LaurentPolynomial.T n, hjT n⟩))
  have hij : ∀ s, i₁ (j s) = i s ⊗ₜ[A] (1 : K) := by
    intro s
    refine LaurentPolynomial.induction_on' s ?_ ?_
    · intro a b ha hb
      rw [map_add, map_add, ha, hb, map_add, TensorProduct.add_tmul]
    · intro n a
      rw [map_mul, map_mul, hjC, hjT, map_mul, hC, hT, hiC, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one, ← Algebra.smul_def, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one]
  have hmap : (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g} :
      Ideal A[T;T⁻¹]).map j = Ideal.span {LaurentPolynomial.C (algebraMap A K f) -
        LaurentPolynomial.T 1 * LaurentPolynomial.C (algebraMap A K g)} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_mul, hjC, hjC, hjT]
  refine ⟨i₁, ?_, hC, hT⟩
  rw [← hmap]
  exact GlobalTheory.T.perfect_tensor_generated_lift p A A[T;T⁻¹] B K K[T;T⁻¹] i _ LaurentPolynomial.C j i₁ hA hK hPQ hcomp hgen
    hC hij

end GlobalTheory.CompanionTheory.PerfBC
