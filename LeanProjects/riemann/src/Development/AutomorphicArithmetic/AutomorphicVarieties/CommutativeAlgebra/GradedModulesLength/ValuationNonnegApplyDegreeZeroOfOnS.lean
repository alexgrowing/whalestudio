import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.IntHolds

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.valuation_nonneg_apply_degreeZero_of_onS :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O) (I : Ideal A), M2 𝒜 I → ∀ ξ : A →ₐ[O] K, OnS I ξ → ∀ b ∈ 𝒜 0, ξ b ≠ 0 → 0 ≤ v (ξ b) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv A _ _ 𝒜 _ _ x I hI ξ hξ b hb hne
  classical
  set M : Submodule O K := Submodule.map ξ.toLinearMap (𝒜 0) with hMdef
  have hker : ∀ f ∈ I, ξ f = 0 := hξ
  let ξ' : (A ⧸ I) →ₐ[O] K := Ideal.Quotient.liftₐ I ξ hker
  have hcomp : ξ.toLinearMap = ξ'.toLinearMap.comp (Ideal.Quotient.mkₐ O I).toLinearMap := by
    apply LinearMap.ext
    intro a
    rfl
  have hMfg : M.FG := by
    rw [hMdef, hcomp, Submodule.map_comp]
    exact Submodule.FG.map _ hI
  haveI : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hMfg
  have hle : Subalgebra.toSubmodule (Algebra.adjoin O {ξ b}) ≤ M := by
    intro z hz
    have hz' : z ∈ Algebra.adjoin O {ξ b} := hz
    clear hz
    rw [hMdef, Submodule.mem_map]
    induction hz' using Algebra.adjoin_induction with
    | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      exact ⟨b, hb, hw.symm⟩
    | algebraMap r =>
      exact ⟨algebraMap O A r, SetLike.algebraMap_mem_graded 𝒜 r, by simp⟩
    | add w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁, e₁⟩ := h₁
      obtain ⟨c₂, hc₂, e₂⟩ := h₂
      exact ⟨c₁ + c₂, add_mem hc₁ hc₂, by simp [← e₁, ← e₂]⟩
    | mul w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁, e₁⟩ := h₁
      obtain ⟨c₂, hc₂, e₂⟩ := h₂
      have hm : c₁ * c₂ ∈ 𝒜 (0 + 0) := SetLike.mul_mem_graded hc₁ hc₂
      rw [add_zero] at hm
      exact ⟨c₁ * c₂, hm, by simp [← e₁, ← e₂]⟩
  haveI : IsNoetherian O (Subalgebra.toSubmodule (Algebra.adjoin O {ξ b})) := isNoetherian_of_le hle
  have hint : IsIntegral O (ξ b) :=
    isIntegral_of_submodule_noetherian (Algebra.adjoin O {ξ b}) inferInstance (ξ b)
      (Algebra.subset_adjoin (Set.mem_singleton _))
  exact int_holds O K v hv (ξ b) hint hne
