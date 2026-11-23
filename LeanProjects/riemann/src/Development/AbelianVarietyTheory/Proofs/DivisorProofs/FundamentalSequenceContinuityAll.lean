import Mathlib
open TensorProduct Polynomial

namespace GlobalTheory

theorem torsion_of_one_tmul_eq_zero (D K M : Type) [CommRing D] [IsDomain D] [Field K]
    [Algebra D K] [FaithfulSMul D K] [AddCommGroup M] [Module D M] (m : M)
    (h : (1 : K) ⊗ₜ[D] m = 0) : ∃ d : D, d ≠ 0 ∧ d • m = 0 := by
  letI : Algebra (FractionRing D) K := FractionRing.liftAlgebra D K
  haveI : IsScalarTower D (FractionRing D) K := FractionRing.isScalarTower_liftAlgebra D K
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (FractionRing D) K)
    (by rw [LinearMap.ker_eq_bot]; exact (algebraMap (FractionRing D) K).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa using this
  have h2 : (1 : FractionRing D) ⊗ₜ[D] m = 0 := by
    have := congrArg ((g.restrictScalars D).rTensor M) h
    simpa [hg1] using this
  obtain ⟨⟨d, hd⟩, hdm⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors D)
    (TensorProduct.mk D (FractionRing D) M 1)).1 h2
  exact ⟨d, nonZeroDivisors.ne_zero hd, hdm⟩

theorem exists_not_mem_ker_smul_mem_map_of_one_tmul_eq_zero (A B K : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Field K] [Algebra A K] (b : B) (h : (1 : K) ⊗ₜ[A] b = 0) :
    ∃ f : A, f ∉ RingHom.ker (algebraMap A K) ∧
      f • b ∈ (RingHom.ker (algebraMap A K)).map (algebraMap A B) := by
  set P := RingHom.ker (algebraMap A K) with hP
  haveI : P.IsPrime := RingHom.ker_isPrime _
  letI : Algebra (A ⧸ P) K := (RingHom.kerLift (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A (A ⧸ P) K := IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  haveI : FaithfulSMul (A ⧸ P) K :=
    (faithfulSMul_iff_algebraMap_injective (A ⧸ P) K).2 (RingHom.kerLift_injective _)
  let I := P.map (algebraMap A B)
  let q : B →ₗ[A] B ⧸ I := (Ideal.Quotient.mkₐ A I).toLinearMap
  let Φ : K ⊗[A] B →ₗ[A] K ⊗[A ⧸ P] (B ⧸ I) :=
    (TensorProduct.mapOfCompatibleSMul (A ⧸ P) A A K (B ⧸ I)) ∘ₗ q.lTensor K
  have h1 : (1 : K) ⊗ₜ[A ⧸ P] (Ideal.Quotient.mk I b) = 0 := by
    have hΦ : Φ ((1 : K) ⊗ₜ[A] b) = (1 : K) ⊗ₜ[A ⧸ P] (Ideal.Quotient.mk I b) := rfl
    rw [← hΦ, h, map_zero]
  obtain ⟨d, hd0, hdb⟩ := torsion_of_one_tmul_eq_zero (A ⧸ P) K (B ⧸ I) _ h1
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨f, fun hf => hd0 (Ideal.Quotient.eq_zero_iff_mem.2 hf), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have : Ideal.Quotient.mk I (f • b) = (Ideal.Quotient.mk P f) • Ideal.Quotient.mk I b := by
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    rfl
  rw [this, hdb]

end GlobalTheory
