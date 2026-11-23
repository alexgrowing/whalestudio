import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.hom_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    Q.ideal.IsHomogeneous 𝒜 ∧ (ideal2 Q).IsHomogeneous 𝒜 ∧ ideal2 Q ≤ Q.ideal := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q
  refine ⟨?_, ?_, ?_⟩
  · refine Ideal.homogeneous_span 𝒜 _ ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    exacts [⟨_, Q.hF i⟩, ⟨_, Q.hG i⟩, ⟨_, Q.hE i⟩, ⟨_, Q.hE' i⟩, ⟨_, (Q.hZ i).1⟩]
  · refine Ideal.homogeneous_span 𝒜 _ ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    exacts [⟨_, sq_mem_neg 𝒜 (Q.hF i)⟩, ⟨_, Q.hG i⟩, ⟨_, sq_mem_pos 𝒜 (Q.hE i)⟩, ⟨_, Q.hE' i⟩, ⟨_, (Q.hZ i).1⟩]
  · refine Ideal.span_le.2 ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact Ideal.pow_mem_of_mem Q.ideal
        (Ideal.subset_span (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))) 2 (by norm_num)
    · exact Ideal.subset_span (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
    · exact Ideal.pow_mem_of_mem Q.ideal
        (Ideal.subset_span (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))) 2 (by norm_num)
    · exact Ideal.subset_span (Or.inl (Or.inr ⟨i, rfl⟩))
    · exact Ideal.subset_span (Or.inr ⟨i, rfl⟩)
