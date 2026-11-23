import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermUnipotentLeftInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermLeviRationalLeftInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasModerateGrowthConstantTerm
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTermSpace_automorphic_properties :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), Bdd S → Sat S → ctSp r S ≤ NInv K (r + s) r ∧ Growth (ctSp r S) ∧ Level (ctSp r S) ∧ Sat (ctSp r S) ∧ ∀ ψ ∈ ctSp r S, ∀ (γ₁ : GL (Fin r) K) (γ₂ : GL (Fin s) K) g, ψ.1 (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g) = ψ.1 g := by
  intro K _ _ r s S hB hS
  have hrt : ∀ (φ φ' : AdelicGLn.AdelicGL K (r + s) → ℂ) (k : AdelicGLn.AdelicGL K (r + s)),
      (∀ x, φ' x = φ (x * k)) → ∀ g, constantTerm r φ (g * k) = constantTerm r φ' g := by
    intro φ φ' k h g
    unfold constantTerm
    simp only [h, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro ψ ⟨φ, hφ, e⟩ X g
    rw [e]
    exact UpperTheory.constantTerm_unipotent_left_invariant K _ r φ.1 (hB.left φ hφ) X g
  · intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨φ, hφ, e⟩ := h
      rw [e]
      exact UpperTheory.hasModerateGrowth_constantTerm K _ r φ.1 (hB.growth φ hφ)
    | zero => exact hasModerateGrowth_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.smul c
  · obtain ⟨L, hL, h⟩ := hB.level
    refine ⟨L, hL, fun ψ hψ u hu g => ?_⟩
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      rw [e]
      exact hrt φ.1 φ.1 _ (fun x => (h φ hφ u hu x).symm) g
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c • ·) hx
  · intro k hk ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      refine Submodule.subset_span ⟨rt k φ, hS k hk φ hφ, funext fun g => ?_⟩
      rw [rt_apply, e]
      exact hrt φ.1 _ k (rt_apply k φ) g
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  · intro ψ hψ γ₁ γ₂ g
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      rw [e]
      exact UpperTheory.constantTerm_levi_rational_left_invariant K r s φ.1 (hB.left φ hφ) γ₁ γ₂ g
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c • ·) hx
