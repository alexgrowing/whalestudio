import Mathlib

open scoped BigOperators

namespace GlobalTheory

theorem exists_common_nat_denominator {R F α : Type*} [CommRing R] [CommRing F] (φ : R →+* F)
    (h : ∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ r = n * x) (g : α → F) (S : Finset α) :
    ∃ n : ℕ, 0 < n ∧ ∀ s ∈ S, ∃ r : R, φ r = n * g s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨n, hn, hS⟩ := ih
    obtain ⟨r, m, hm, hr⟩ := h (g a)
    refine ⟨n * m, Nat.mul_pos hn hm, fun s hs => ?_⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact ⟨n * r, by rw [map_mul, map_natCast, hr]; push_cast; ring⟩
    · obtain ⟨r', hr'⟩ := hS s hs
      exact ⟨m * r', by rw [map_mul, map_natCast, hr']; push_cast; ring⟩

theorem exists_homogeneous_lift_nat_mul {R F J : Type*} [CommRing R] [CommRing F] (φ : R →+* F)
    (h : ∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ r = n * x) (G : MvPolynomial J F) (d : ℕ)
    (hG : G.IsHomogeneous d) :
    ∃ (n : ℕ) (G' : MvPolynomial J R), 0 < n ∧ G'.IsHomogeneous d ∧
      MvPolynomial.map φ G' = (n : MvPolynomial J F) * G := by
  classical
  obtain ⟨n, hn, hS⟩ := exists_common_nat_denominator φ h (fun s => G.coeff s) G.support
  choose! r hr using hS
  refine ⟨n, ∑ s ∈ G.support, MvPolynomial.monomial s (r s), hn, ?_, ?_⟩
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s hs => ?_
    refine MvPolynomial.isHomogeneous_monomial _ ?_
    have := hG (MvPolynomial.mem_support_iff.1 hs)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  · rw [map_sum]
    conv_rhs => rw [G.as_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [MvPolynomial.map_monomial, hr s hs, ← map_natCast (MvPolynomial.C : F →+* MvPolynomial J F),
      MvPolynomial.C_mul_monomial]

theorem cone_closure_arc_of_integral_image_reduction :
    (∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W) → (∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ) → ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∀ (K J ι : Type) [Field K] [CharZero K] [Fintype J] [Finite ι] (ψ : R →+* K), (∀ r, φ r = 0 → ψ r = 0) → ∀ (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra ℚ (A i)], (∀ i, Algebra.FiniteType ℚ (A i)) → ∀ (χ : ∀ i, R →+* A i), (∀ i r, φ r = 0 → χ i r = 0) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J R) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.eval₂ (χ i) (w i) G = 0) → MvPolynomial.eval₂ ψ v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ r : R, f (χ i r) = algebraMap W (FractionRing W) (algebraMap K W (ψ r))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro H1 H2 R _ φ hφ K J ι _ _ _ _ ψ hψ A _ _ hA χ hχ w v hv hG
  obtain ⟨F, _, _, φ', hF, hlift⟩ := H2 R φ hφ
  obtain ⟨ψ', hψ'⟩ := hlift K ψ hψ
  choose χ' hχ' using fun i => hlift (A i) (χ i) (hχ i)
  letI : Algebra F K := ψ'.toAlgebra
  letI : ∀ i, Algebra F (A i) := fun i => (χ' i).toAlgebra
  have hA' : ∀ i, Algebra.FiniteType F (A i) := fun i => by
    haveI : IsScalarTower ℚ F (A i) :=
      IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI := hA i
    exact Algebra.FiniteType.of_restrictScalars_finiteType ℚ F (A i)
  obtain ⟨i, W, _, _, _, _, f, s, w', h1, h2, h3, h4⟩ := H1 F K J ι A hA' w v hv (by
    intro G d hd h0
    obtain ⟨n, G', hn, hG', hmap⟩ := exists_homogeneous_lift_nat_mul φ' hF G d hd
    have key := hG G' d hG' (fun i => by
      have : MvPolynomial.eval₂ (χ i) (w i) G'
          = MvPolynomial.aeval (w i) (MvPolynomial.map φ' G') := by
        rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← hχ' i]; rfl
      rw [this, hmap, map_mul, h0 i, mul_zero])
    have : MvPolynomial.eval₂ ψ v G' = MvPolynomial.aeval v (MvPolynomial.map φ' G') := by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← hψ']; rfl
    rw [this, hmap, map_mul, map_natCast] at key
    exact (mul_eq_zero.1 key).resolve_left (Nat.cast_ne_zero.2 hn.ne'))
  refine ⟨i, W, inferInstance, inferInstance, inferInstance, inferInstance, f, s, w', h1, h2, fun r => ?_, h4⟩
  have := h3 (φ' r)
  rw [← hχ' i, ← hψ']
  exact this

end GlobalTheory
