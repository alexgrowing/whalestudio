import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.OzTwoMulEqPow

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.kill_pow {O B A κ : Type} [CommRing O] [CommRing B] [CommRing A] [Algebra O A]
    [Algebra B A] [Field κ] [Algebra O κ] (ξ : A →ₐ[O] κ) (N : Submodule B A) (hN : ∀ f ∈ N, ξ f = 0)
    (n : ℕ) (hn : n ≠ 0) : ∀ f ∈ N ^ n, ξ f = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  intro f hf
  rw [pow_succ] at hf
  refine Submodule.mul_induction_on hf (fun a _ b hb => ?_) (fun a b ha hb => ?_)
  · rw [map_mul, hN b hb, mul_zero]
  · rw [map_add, ha, hb, add_zero]

theorem UpperTheory.V.Alg.M.sign_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (κ : Type) [Field κ] [Algebra O κ] (ξ : A →ₐ[O] κ),
      (¬ NegZero 𝒜 ξ ↔ ∃ f ∈ 𝒜 (-2), ξ f ≠ 0) ∧ (¬ PosZero 𝒜 ξ ↔ ∃ g ∈ 𝒜 2, ξ g ≠ 0) := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx κ _ _ ξ
  have hp := UpperTheory.V.Alg.M.oz_two_mul_eq_pow O A 𝒜 x hx
  refine ⟨⟨fun h => ?_, ?_⟩, ⟨fun h => ?_, ?_⟩⟩
  · by_contra hc
    push Not at hc
    refine h fun j hj f hf => ?_
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -j by omega)
    have h2 : f * f ∈ oz 𝒜 (-(2 * (n : ℤ))) := by
      have := SetLike.GradedMul.mul_mem hf hf
      rwa [show j + j = -(2 * (n : ℤ)) by omega] at this
    rw [(hp n).1] at h2
    have h3 := UpperTheory.V.Alg.M.kill_pow ξ (oz 𝒜 (-2)) hc n (by omega) _ h2
    rw [map_mul] at h3
    exact mul_self_eq_zero.1 h3
  · rintro ⟨f, hf, h0⟩ h
    exact h0 (h (-2) (by norm_num) f hf)
  · by_contra hc
    push Not at hc
    refine h fun j hj f hf => ?_
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ j by omega)
    have h2 : f * f ∈ oz 𝒜 (2 * (n : ℤ)) := by
      have := SetLike.GradedMul.mul_mem hf hf
      rwa [show j + j = 2 * (n : ℤ) by omega] at this
    rw [(hp n).2] at h2
    have h3 := UpperTheory.V.Alg.M.kill_pow ξ (oz 𝒜 2) hc n (by omega) _ h2
    rw [map_mul] at h3
    exact mul_self_eq_zero.1 h3
  · rintro ⟨f, hf, h0⟩ h
    exact h0 (h 2 (by norm_num) f hf)
