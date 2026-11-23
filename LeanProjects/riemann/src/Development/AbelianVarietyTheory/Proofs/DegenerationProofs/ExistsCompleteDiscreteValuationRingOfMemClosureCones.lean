import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDiscreteValuationRingOfMemClosureC
open scoped BigOperators TensorProduct

namespace GlobalTheory

theorem sum_mul_eq_zero_of_forall_dual {F K σ : Type} [Field F] [Field K] [Algebra F K]
    (S : Finset σ) (c m : σ → K)
    (h : ∀ l : K →ₗ[F] F, ∑ s ∈ S, l (c s) • m s = 0) : ∑ s ∈ S, c s * m s = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F K
  let T := S.biUnion fun s => (b.repr (c s)).support
  have hc : ∀ s ∈ S, c s = ∑ j ∈ T, b.coord j (c s) • b j := fun s hs => by
    conv_lhs => rw [← b.linearCombination_repr (c s)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset (s := T)]
    · rfl
    · exact Finset.subset_biUnion_of_mem (fun s => (b.repr (c s)).support) hs
    · simp
  calc ∑ s ∈ S, c s * m s = ∑ s ∈ S, ∑ j ∈ T, b j * (b.coord j (c s) • m s) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        conv_lhs => rw [hc s hs]
        rw [Finset.sum_mul]
        simp
    _ = 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← Finset.mul_sum, h, mul_zero]

theorem eval_eq_zero_of_aeval_tmul_eq_zero {F K J ι : Type} [Field F] [Field K] [Algebra F K]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)] (w : ∀ i, J → A i) (v : J → K)
    (h : ∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d →
      (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0)
    (G : MvPolynomial J K) (d : ℕ) (hG : G.IsHomogeneous d)
    (h0 : ∀ i, MvPolynomial.aeval (fun j => (1 : K) ⊗ₜ[F] w i j) G = 0) :
    MvPolynomial.eval v G = 0 := by
  rw [MvPolynomial.eval_eq]
  refine sum_mul_eq_zero_of_forall_dual (F := F) _ _ _ fun l => ?_
  have key : ∀ (B : Type) [CommRing B] [Algebra F B] (u : J → B),
      MvPolynomial.aeval u (∑ s ∈ G.support, MvPolynomial.monomial s (l (G.coeff s))) =
        ∑ s ∈ G.support, l (G.coeff s) • ∏ j ∈ s.support, u j ^ s j := fun B _ _ u => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.aeval_monomial, Algebra.smul_def]
    rfl
  rw [← key]
  refine h _ d (MvPolynomial.IsHomogeneous.sum _ _ _ fun s hs => ?_) fun i => ?_
  · refine MvPolynomial.isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_weight_one]
    exact hG (MvPolynomial.mem_support_iff.mp hs)
  · rw [key]
    have h1 := congrArg ((TensorProduct.lid F (A i)).toLinearMap ∘ₗ l.rTensor (A i)) (h0 i)
    rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun s _ => ?_
    have h2 : algebraMap K (K ⊗[F] A i) (G.coeff s) * ∏ j ∈ s.support, ((1 : K) ⊗ₜ[F] w i j) ^ s j
        = G.coeff s ⊗ₜ[F] ∏ j ∈ s.support, w i j ^ s j := by
      have : ∏ j ∈ s.support, ((1 : K) ⊗ₜ[F] w i j) ^ s j
          = (1 : K) ⊗ₜ[F] ∏ j ∈ s.support, w i j ^ s j := by
        simp only [← Algebra.TensorProduct.includeRight_apply (R := F) (A := K), map_prod, map_pow]
      rw [this]
      simp
    rw [h2]
    simp

theorem exists_complete_discreteValuationRing_of_mem_closure_cones :
    ∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro F K J ι _ _ _ _ _ A _ _ hA w v hv h
  classical
  have hN : ∀ i, IsNoetherianRing (K ⊗[F] A i) := fun i =>
    Algebra.FiniteType.isNoetherianRing K _
  by_cases hex : ∃ (i : ι) (P : Ideal (K ⊗[F] A i)), P ∈ minimalPrimes (K ⊗[F] A i) ∧
      ∀ (G : MvPolynomial J K) (d : ℕ), G.IsHomogeneous d →
        MvPolynomial.aeval (fun j => Ideal.Quotient.mk P ((1 : K) ⊗ₜ[F] w i j)) G = 0 →
        MvPolynomial.eval v G = 0
  · obtain ⟨i, P, hP, hG⟩ := hex
    have : P.IsPrime := hP.1.1
    obtain ⟨W, _, _, _, _, f, s, w', h1, h2, h3⟩ :=
      exists_complete_discreteValuationRing_of_mem_closure_cone K ((K ⊗[F] A i) ⧸ P) J
        inferInstance _ v hv hG
    refine ⟨i, W, inferInstance, inferInstance, inferInstance, inferInstance,
      f.toRingHom.comp ((Ideal.Quotient.mk P).comp
        (Algebra.TensorProduct.includeRight (R := F) (A := K) (B := A i)).toRingHom),
      s, w', h1, h2, fun x => ?_, h3⟩
    rw [← IsScalarTower.algebraMap_apply K W (FractionRing W), ← f.commutes]
    change f (Ideal.Quotient.mk P (Algebra.TensorProduct.includeRight (R := F) (A := K)
      (algebraMap F (A i) x))) = f (Ideal.Quotient.mk P (algebraMap K _ (algebraMap F K x)))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  · exfalso
    push_neg at hex
    choose G d hG hG0 hGv using hex
    have : ∀ i, Finite (minimalPrimes (K ⊗[F] A i)) := fun i =>
      (minimalPrimes.finite_of_isNoetherianRing _).to_subtype
    letI : Fintype (Σ i, minimalPrimes (K ⊗[F] A i)) := Fintype.ofFinite _
    let H : MvPolynomial J K := ∏ x : Σ i, minimalPrimes (K ⊗[F] A i), G x.1 x.2.1 x.2.2
    have hH : H.IsHomogeneous (∑ x : Σ i, minimalPrimes (K ⊗[F] A i), d x.1 x.2.1 x.2.2) :=
      MvPolynomial.IsHomogeneous.prod _ _ _ fun x _ => hG _ _ _
    have hHv : MvPolynomial.eval v H ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr fun x _ => hGv _ _ _
    have hnil : ∀ i, IsNilpotent (MvPolynomial.aeval (fun j => (1 : K) ⊗ₜ[F] w i j) H) := by
      intro i
      rw [nilpotent_iff_mem_prime]
      intro Q hQ
      obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := Q) bot_le
      refine hPQ ?_
      rw [map_prod]
      refine Ideal.prod_mem P (Finset.mem_univ
        (⟨i, P, hP⟩ : Σ i, minimalPrimes (K ⊗[F] A i))) ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hG0 i P hP]
      exact MvPolynomial.comp_aeval_apply _ (Ideal.Quotient.mkₐ K P) _
    choose n hn using hnil
    letI : Fintype ι := Fintype.ofFinite ι
    refine pow_ne_zero (∑ i, n i) hHv ?_
    rw [← map_pow]
    refine eval_eq_zero_of_aeval_tmul_eq_zero A w v h _ _ (hH.pow _) fun i => ?_
    rw [map_pow]
    exact pow_eq_zero_of_le (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)) (hn i)

end GlobalTheory
