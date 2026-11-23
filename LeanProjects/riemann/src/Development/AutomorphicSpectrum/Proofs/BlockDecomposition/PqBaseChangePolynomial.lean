import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorGeneratedLiftStatement
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Perfection

theorem pq_baseChange_polynomial : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : Polynomial A →ₐ[A] B) (h : Polynomial A), Pf p A → Pf p K → PQ p (i : Polynomial A →+* B) (Ideal.span {h}) → ∃ i₁ : Polynomial K →+* B ⊗[A] K, PQ p i₁ (Ideal.span {h.map (algebraMap A K)}) ∧ (∀ a, i₁ (Polynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ i₁ Polynomial.X = i Polynomial.X ⊗ₜ[A] (1 : K) := by
  intro p _ A _ B _ _ K _ _ i h hA hK hPQ
  let i₁ : Polynomial K →+* B ⊗[A] K :=
    Polynomial.eval₂RingHom (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom
      (i Polynomial.X ⊗ₜ[A] (1 : K))
  have hC : ∀ a, i₁ (Polynomial.C a) = (1 : B) ⊗ₜ[A] a := by
    intro a
    simp [i₁]
  have hX : i₁ Polynomial.X = i Polynomial.X ⊗ₜ[A] (1 : K) := by
    simp [i₁]
  have hj : ∀ s : Polynomial A, i₁ (Polynomial.mapRingHom (algebraMap A K) s) = i s ⊗ₜ[A] (1 : K) := by
    intro s
    induction s using Polynomial.induction_on with
    | C a =>
      have h1 : i (Polynomial.C a) = algebraMap A B a := by
        rw [← Polynomial.algebraMap_eq]
        exact i.commutes a
      rw [Polynomial.coe_mapRingHom, Polynomial.map_C, hC, h1, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add f g hf hg =>
      rw [map_add, map_add, hf, hg, map_add, TensorProduct.add_tmul]
    | monomial n a ih =>
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial A)
          = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      rw [e, map_mul, map_mul, ih, map_mul]
      have e2 : Polynomial.mapRingHom (algebraMap A K) (Polynomial.X : Polynomial A) = Polynomial.X := by
        simp
      rw [e2, hX, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simp only [map_mul]
  have hcl : Subring.closure (Set.range (Polynomial.C : K →+* Polynomial K) ∪
      Set.range (Polynomial.mapRingHom (algebraMap A K))) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    induction f using Polynomial.induction_on with
    | C a => exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    | add f g hf hg => exact Subring.add_mem _ (hf trivial) (hg trivial)
    | monomial n a ih =>
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial K)
          = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      rw [e]
      refine Subring.mul_mem _ (ih trivial) (Subring.subset_closure (Or.inr ⟨Polynomial.X, ?_⟩))
      simp
  have hcomp : (Polynomial.C : K →+* Polynomial K).comp (algebraMap A K)
      = (Polynomial.mapRingHom (algebraMap A K)).comp (algebraMap A (Polynomial A)) := by
    ext a
    simp [Polynomial.algebraMap_apply]
  have key := GlobalTheory.T.perfect_tensor_generated_lift p A (Polynomial A) B K (Polynomial K) i (Ideal.span {h})
    Polynomial.C (Polynomial.mapRingHom (algebraMap A K)) i₁ hA hK hPQ hcomp hcl hC hj
  refine ⟨i₁, ?_, hC, hX⟩
  rw [Ideal.map_span, Set.image_singleton] at key
  simpa using key

end GlobalTheory.CompanionTheory.Perfection
