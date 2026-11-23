import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMemOfSpanBaseChange
import GroundTheory.Brauer.BaseChangeCSA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRatAlgebraDecompFactorwiseStatement

open scoped TensorProduct
open Polynomial

namespace GlobalTheory.SkNoFactor

theorem minpoly_eq_of_aeval_of_linearIndependent {L A : Type} [Field L] [Ring A] [Algebra L A]
    (p : L[X]) (y : A) (hm : p.Monic) (hy : aeval y p = 0)
    (hind : ∀ c : Fin p.natDegree → L, ∑ j, c j • y ^ (j : ℕ) = 0 → c = 0) : minpoly L y = p := by
  have hi : IsIntegral L y := ⟨p, hm, by rwa [← aeval_def]⟩
  have hdvd : minpoly L y ∣ p := minpoly.dvd L y hy
  have hle : p.natDegree ≤ (minpoly L y).natDegree := by
    by_contra hlt
    push_neg at hlt
    have hsum := aeval_eq_sum_range' hlt y
    rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly L y).coeff i • y ^ i)] at hsum
    have hc := hind (fun i => (minpoly L y).coeff i) hsum.symm
    apply minpoly.ne_zero hi
    ext i
    rw [coeff_zero]
    by_cases h : i < p.natDegree
    · exact congrFun hc ⟨i, h⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) hdvd hle
  rw [this, hm.leadingCoeff, C_1, one_mul]

theorem minpoly_one_tmul {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (K : Type) [Field K] [Algebra F K] (y : B) :
    minpoly K ((1 : K) ⊗ₜ[F] y) = (minpoly F y).map (algebraMap F K) := by
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K y hzi
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
    (by rw [natDegree_map]; exact hge)
  rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]

theorem exists_unit_conj_baseChange : ∀ (S F B : Type) [Field S] [CharZero S] [Field F] [Algebra ℚ F]
    [FiniteDimensional ℚ F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B]
    [FiniteDimensional F B] (n : ℕ), Module.finrank F B = n ^ 2 → ∀ (x₀ : B) (x : S ⊗[ℚ] B),
    (minpoly F x₀).Separable → (minpoly F x₀).natDegree = n →
    (∑ i ∈ Finset.range (n + 1), ((1 : S) ⊗ₜ[ℚ] algebraMap F B ((minpoly F x₀).coeff i)) * x ^ i = 0) →
    (∀ c : Fin n → S ⊗[ℚ] F, ∑ j, Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom ℚ F B) (c j) *
      x ^ (j : ℕ) = 0 → c = 0) →
    ∃ g : (S ⊗[ℚ] B)ˣ, (g : S ⊗[ℚ] B) * ((1 : S) ⊗ₜ[ℚ] x₀) = x * g := by
  intro S F B _ _ _ _ _ _ _ _ _ _ _ _ n hn x₀ x hsep hdeg hP hind
  classical
  obtain ⟨ι, _, L, _, _, _, Φ, ψ, hΦ1, hΦ2⟩ := GlobalTheory.T.tensor_rat_algebra_decomp_factorwise S F B
  have hcomp : ∀ i, ∃ u : (L i ⊗[F] B)ˣ, (u : L i ⊗[F] B) * ((1 : L i) ⊗ₜ[F] x₀) = Φ x i * u := by
    intro i
    haveI : Infinite (L i) := Infinite.of_injective (Nat.cast : ℕ → L i) Nat.cast_injective
    have hn' : Module.finrank (L i) (L i ⊗[F] B) = n ^ 2 := by rw [Module.finrank_baseChange, hn]
    have h0 : minpoly (L i) ((1 : L i) ⊗ₜ[F] x₀) = (minpoly F x₀).map (algebraMap F (L i)) :=
      minpoly_one_tmul (L i) x₀
    have hmonic : ((minpoly F x₀).map (algebraMap F (L i))).Monic :=
      (minpoly.monic (IsIntegral.of_finite F x₀)).map _
    have hdegm : ((minpoly F x₀).map (algebraMap F (L i))).natDegree = n := by rw [natDegree_map, hdeg]
    have hcoef : ∀ c : F, Φ ((1 : S) ⊗ₜ[ℚ] algebraMap F B c) i =
        algebraMap (L i) (L i ⊗[F] B) (algebraMap F (L i) c) := by
      intro c
      rw [hΦ1]
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        ← Algebra.TensorProduct.one_def]
    have hy : aeval (Φ x i) ((minpoly F x₀).map (algebraMap F (L i))) = 0 := by
      have := congrArg (fun w => Φ w i) hP
      simp only [map_sum, map_mul, map_pow, map_zero, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply,
        Pi.zero_apply, hcoef] at this
      rw [aeval_eq_sum_range' (n := n + 1) (by rw [hdegm]; omega), ← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeff_map, Algebra.smul_def]
    have hli : ∀ c : Fin ((minpoly F x₀).map (algebraMap F (L i))).natDegree → L i,
        ∑ j, c j • Φ x i ^ (j : ℕ) = 0 → c = 0 := by
      rw [hdegm]
      intro c hc
      have hz := hind (fun j => ψ.symm (Pi.single i (c j))) (by
        apply Φ.injective
        rw [map_zero]
        funext k
        simp only [map_sum, map_mul, map_pow, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hΦ2,
          RingEquiv.apply_symm_apply, Pi.zero_apply]
        by_cases hk : k = i
        · subst hk
          simpa [Pi.single_eq_same, Algebra.smul_def] using hc
        · simp [Pi.single_eq_of_ne hk])
      funext j
      have := congrArg (fun w => ψ (w j) i) hz
      simpa using this
    have hmin : minpoly (L i) (Φ x i) = minpoly (L i) ((1 : L i) ⊗ₜ[F] x₀) := by
      rw [h0]; exact minpoly_eq_of_aeval_of_linearIndependent _ _ hmonic hy hli
    exact GlobalTheory.LKInv.exists_unit_conj_of_minpoly_eq (L i) (L i ⊗[F] B) n hn' _ _
      (by rw [h0]; exact hsep.map) (by rw [h0, hdegm]) hmin
  choose u hu using hcomp
  let v : ((i : ι) → L i ⊗[F] B)ˣ := MulEquiv.piUnits.symm u
  refine ⟨Units.map Φ.symm.toMonoidHom v, ?_⟩
  apply Φ.injective
  rw [map_mul, map_mul]
  funext i
  simp [v, hΦ1, hu i]

end GlobalTheory.SkNoFactor
