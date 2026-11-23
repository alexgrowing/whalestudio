import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.OzTwoMulEqPow

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.fix_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ σ : 𝒜 0 →ₐ[O] K, idD 𝒜 ≤ RingHom.ker σ → (∀ b : 𝒜 0, (b : A) ∈ Q.ideal → σ b = 0) →
      ∃ ξ : A →ₐ[O] K, OnS Q.ideal ξ ∧ NegZero 𝒜 ξ ∧ PosZero 𝒜 ξ ∧ res0 𝒜 ξ = σ := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q σ hid hQ
  have hcoe : ∀ z (hz : z ∈ 𝒜 0), DirectSum.decompose 𝒜 z 0 = ⟨z, hz⟩ :=
    fun z hz => Subtype.ext (DirectSum.decompose_of_mem_same 𝒜 hz)
  have dmul : ∀ (i : ℤ) (z : A), z ∈ 𝒜 i → ∀ b : A,
      (DirectSum.decompose 𝒜 (z * b) 0 : A) = z * (DirectSum.decompose 𝒜 b (-i) : A) := by
    intro i z hz b
    have h := DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (j := -i) hz (b := b)
    rwa [add_neg_cancel] at h
  have kill : ∀ c : 𝒜 0, ∀ f ∈ 𝒜 (-2), ∀ g ∈ 𝒜 2, (c : A) = f * g → σ c = 0 := by
    intro c f hf g hg h
    exact (RingHom.mem_ker).1 (hid (Ideal.subset_span ⟨f, hf, g, hg, h⟩))
  have kill1 : ∀ c : 𝒜 0, ∀ f ∈ 𝒜 (-1), ∀ g ∈ 𝒜 1, (c : A) = f * g → σ c = 0 := by
    intro c f hf g hg h
    have hff : f * f ∈ 𝒜 (-2) := by
      convert SetLike.mul_mem_graded hf hf using 2
      norm_num
    have hgg : g * g ∈ 𝒜 2 := by
      convert SetLike.mul_mem_graded hg hg using 2
      norm_num
    have h2 : σ (c * c) = 0 := kill (c * c) (f * f) hff (g * g) hgg (by
      rw [SetLike.GradeZero.coe_mul, h]
      ring)
    rw [map_mul] at h2
    exact mul_self_eq_zero.1 h2
  obtain ⟨S, hS, hgen⟩ := hW.gen
  have key : ∀ z ∈ S, ∀ b : A, σ (DirectSum.decompose 𝒜 (z * b) 0) = 0 := by
    intro z hz b
    rcases hS z hz with h | h | h | h
    · refine kill _ z h _ (DirectSum.decompose 𝒜 b 2).2 ?_
      rw [dmul _ z h b, neg_neg]
    · refine kill1 _ z h _ (DirectSum.decompose 𝒜 b 1).2 ?_
      rw [dmul _ z h b, neg_neg]
    · refine kill1 _ _ (DirectSum.decompose 𝒜 b (-1)).2 z h ?_
      rw [dmul _ z h b, mul_comm]
    · refine kill _ _ (DirectSum.decompose 𝒜 b (-2)).2 z h ?_
      rw [dmul _ z h b, mul_comm]
  have h0 : ∀ z ∈ 𝒜 0, ∀ b : A, σ (DirectSum.decompose 𝒜 (z * b) 0) =
      σ (DirectSum.decompose 𝒜 z 0) * σ (DirectSum.decompose 𝒜 b 0) := by
    intro z hz b
    have h1 : DirectSum.decompose 𝒜 (z * b) 0 = ⟨z, hz⟩ * DirectSum.decompose 𝒜 b 0 := by
      apply Subtype.ext
      rw [SetLike.GradeZero.coe_mul]
      have h := DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (j := 0) hz (b := b)
      rw [add_zero] at h
      exact h
    rw [h1, hcoe z hz, map_mul]
  have hmul : ∀ a b : A, σ (DirectSum.decompose 𝒜 (a * b) 0) =
      σ (DirectSum.decompose 𝒜 a 0) * σ (DirectSum.decompose 𝒜 b 0) := by
    intro a b
    have ha : a ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ S) := by
      rw [hgen]
      trivial
    induction ha using Algebra.adjoin_induction generalizing b with
    | mem z hz =>
      rcases hz with hz | hz
      · exact h0 z hz b
      · have hz0 : DirectSum.decompose 𝒜 z 0 = 0 := by
          apply Subtype.ext
          rcases hS z hz with h | h | h | h <;>
            (rw [DirectSum.decompose_of_mem_ne 𝒜 h (by norm_num)]; rfl)
        rw [key z hz b, hz0, map_zero, zero_mul]
    | algebraMap c => exact h0 _ (SetLike.algebraMap_mem_graded 𝒜 c) b
    | add a a' _ _ iha iha' =>
      rw [add_mul, DirectSum.decompose_add, DirectSum.add_apply, map_add, iha, iha',
        DirectSum.decompose_add, DirectSum.add_apply, map_add, add_mul]
    | mul a a' _ _ iha iha' =>
      rw [mul_assoc, iha (a' * b), iha' b, iha a']
      ring
  let ξ : A →ₐ[O] K :=
    { toFun := fun a => σ (DirectSum.decompose 𝒜 a 0)
      map_one' := by
        show σ (DirectSum.decompose 𝒜 1 0) = 1
        rw [show DirectSum.decompose 𝒜 (1 : A) 0 = 1 from Subtype.ext (by
          rw [DirectSum.decompose_of_mem_same 𝒜 (SetLike.one_mem_graded 𝒜),
            SetLike.GradeZero.coe_one]), map_one]
      map_mul' := hmul
      map_zero' := by simp
      map_add' := by
        intro a b
        show σ (DirectSum.decompose 𝒜 (a + b) 0) =
          σ (DirectSum.decompose 𝒜 a 0) + σ (DirectSum.decompose 𝒜 b 0)
        rw [DirectSum.decompose_add, DirectSum.add_apply, map_add]
      commutes' := by
        intro c
        show σ (DirectSum.decompose 𝒜 (algebraMap O A c) 0) = algebraMap O K c
        rw [hcoe _ (SetLike.algebraMap_mem_graded 𝒜 c)]
        rw [show (⟨algebraMap O A c, SetLike.algebraMap_mem_graded 𝒜 c⟩ : 𝒜 0) =
          algebraMap O (𝒜 0) c from Subtype.ext (SetLike.GradeZero.coe_algebraMap 𝒜 c).symm]
        exact σ.commutes c }
  have hξ : ∀ a, ξ a = σ (DirectSum.decompose 𝒜 a 0) := fun a => rfl
  have hne : ∀ j : ℤ, j ≠ 0 → ∀ f ∈ 𝒜 j, ξ f = 0 := by
    intro j hj f hf
    rw [hξ, show DirectSum.decompose 𝒜 f 0 = 0 from Subtype.ext (by
      rw [DirectSum.decompose_of_mem_ne 𝒜 hf hj]; rfl), map_zero]
  refine ⟨ξ, ?_, ?_, ?_, ?_⟩
  · intro f hf
    have hle : Q.ideal ≤ RingHom.ker ξ := by
      unfold Eqns.ideal
      rw [Ideal.span_le]
      intro y hy
      rw [SetLike.mem_coe, RingHom.mem_ker]
      rcases hy with ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · exact hne (-1) (by norm_num) _ (Q.hF i)
      · exact hne (-2) (by norm_num) _ (Q.hG i)
      · exact hne 1 (by norm_num) _ (Q.hE i)
      · exact hne 2 (by norm_num) _ (Q.hE' i)
      · rw [hξ, hcoe _ (Q.hZ i).1]
        exact hQ ⟨Q.Z i, (Q.hZ i).1⟩ (Ideal.subset_span (Set.mem_union_right _ ⟨i, rfl⟩))
    exact (RingHom.mem_ker).1 (hle hf)
  · intro j hj f hf
    exact hne j (by omega) f hf
  · intro j hj f hf
    exact hne j (by omega) f hf
  · refine AlgHom.ext fun b => ?_
    show σ (DirectSum.decompose 𝒜 ((b : 𝒜 0) : A) 0) = σ b
    rw [DirectSum.decompose_coe, DirectSum.of_eq_same]
