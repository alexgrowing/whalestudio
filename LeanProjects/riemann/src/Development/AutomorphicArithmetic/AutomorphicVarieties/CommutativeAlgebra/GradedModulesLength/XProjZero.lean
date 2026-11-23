import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SignHolds

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
  [Field K] [Algebra O K]

private theorem proj_same {j : ℤ} {f : A} (hf : f ∈ 𝒜 j) : GradedAlgebra.proj 𝒜 j f = f := by
  rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hf]

private theorem proj_ne {i j : ℤ} {f : A} (hf : f ∈ 𝒜 i) (h : i ≠ j) : GradedAlgebra.proj 𝒜 j f = 0 := by
  rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hf h]

private theorem x_proj_zero (x : A →ₐ[O] O) (hx : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0) (u : A) :
    x (GradedAlgebra.proj 𝒜 0 u) = x u := by
  induction u using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i m =>
    by_cases hi : i = 0
    · subst hi
      rw [proj_same 𝒜 m.2]
    · rw [proj_ne 𝒜 m.2 hi, map_zero, hx i hi _ m.2]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

private theorem kill_sq (x : A →ₐ[O] O) (hx : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0) (ξ : A →ₐ[O] K) (j : ℤ)
    (h : ∀ a b, a + b = j → ∀ u ∈ 𝒜 a, ∀ v ∈ 𝒜 b, x u = 0 → x v = 0 → ξ u * ξ v = 0)
    (f : A) (hf : f ∈ RingHom.ker x ^ 2) : ξ (GradedAlgebra.proj 𝒜 j f) = 0 := by
  classical
  have hc : ∀ u : A, x u = 0 → ∀ a, x (DirectSum.decompose 𝒜 u a : A) = 0 := by
    intro u hu a
    by_cases ha : a = 0
    · subst ha
      rw [← GradedAlgebra.proj_apply, x_proj_zero 𝒜 x hx, hu]
    · exact hx a ha _ (SetLike.coe_mem _)
  rw [sq] at hf
  refine Submodule.mul_induction_on hf (fun u hu v hv => ?_) (fun a b ha hb => by rw [map_add, map_add, ha, hb, add_zero])
  rw [← DirectSum.sum_support_decompose 𝒜 u, ← DirectSum.sum_support_decompose 𝒜 v, Finset.sum_mul_sum]
  simp only [map_sum]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  have hm : (DirectSum.decompose 𝒜 u a : A) * (DirectSum.decompose 𝒜 v b : A) ∈ 𝒜 (a + b) :=
    SetLike.GradedMul.mul_mem (SetLike.coe_mem _) (SetLike.coe_mem _)
  by_cases hab : a + b = j
  · rw [proj_same 𝒜 (hab ▸ hm), map_mul]
    exact h a b hab _ (SetLike.coe_mem _) _ (SetLike.coe_mem _) (hc u hu a) (hc v hv b)
  · rw [proj_ne 𝒜 hm hab, map_zero]

private theorem kill_part [IsDomain O] [FaithfulSMul O K] (x : A →ₐ[O] O)
    (hx : ∀ j, j ≠ 0 → ∀ f ∈ 𝒜 j, x f = 0) (ξ : A →ₐ[O] K) (j : ℤ) (hj : j ≠ 0)
    (h : ∀ a b, a + b = j → ∀ u ∈ 𝒜 a, ∀ v ∈ 𝒜 b, x u = 0 → x v = 0 → ξ u * ξ v = 0)
    {ι : Type} (F : ι → A) (hF : ∀ i, F i ∈ 𝒜 j) (hξ : ∀ i, ξ (F i) = 0) (hs : SpansCot x 𝒜 j F)
    (f : A) (hf : f ∈ 𝒜 j) : ξ f = 0 := by
  have hcan : ∀ c : O, c ≠ 0 → ∀ y : K, c • y = 0 → y = 0 := by
    intro c hc y hy
    rw [Algebra.smul_def] at hy
    exact (mul_eq_zero.1 hy).resolve_left
      (fun h0 => hc (FaithfulSMul.algebraMap_injective O K (by rw [h0, map_zero])))
  let L : A →ₗ[O] K := ξ.toLinearMap ∘ₗ GradedAlgebra.proj 𝒜 j
  have hL : satSq x ≤ LinearMap.ker L := by
    rintro g ⟨c, hc, hg⟩
    refine hcan c hc _ ?_
    rw [← map_smul]
    exact kill_sq 𝒜 x hx ξ j h _ hg
  have hL' : ∀ g ∈ 𝒜 j, (satSq x).liftQ L hL ((satSq x).mkQ g) = ξ g := by
    intro g hg
    show ξ (GradedAlgebra.proj 𝒜 j g) = ξ g
    rw [proj_same 𝒜 hg]
  obtain ⟨c, hc, hp⟩ := hs ((satSq x).mkQ f) ⟨f, ⟨hf, hx j hj f hf⟩, rfl⟩
  have hle : cotSpan x F ≤ LinearMap.ker ((satSq x).liftQ L hL) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact (hL' _ (hF i)).trans (hξ i)
  have h1 := LinearMap.mem_ker.1 (hle hp)
  rw [map_smul, hL' f hf] at h1
  exact hcan c hc _ h1

end SlopeTestRemainingChoices

theorem UpperTheory.V.Alg.M.ct_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    SpansCot x 𝒜 (-1) Q.F → SpansCot x 𝒜 (-2) Q.G → ∀ ξ : A →ₐ[O] K, OnS Q.ideal ξ → PosZero 𝒜 ξ →
      Same0 𝒜 ξ ((Algebra.ofId O K).comp x) → NegZero 𝒜 ξ := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q hF hG ξ hS hP h0
  have hnn : ∀ a, 0 ≤ a → ∀ u ∈ 𝒜 a, x u = 0 → ξ u = 0 := by
    intro a ha u hu hxu
    rcases ha.eq_or_lt with rfl | ha
    · rw [h0 u hu, AlgHom.comp_apply, hxu, map_zero]
    · exact hP a ha u hu
  have h1 : ∀ f ∈ 𝒜 (-1), ξ f = 0 := by
    refine kill_part 𝒜 x hW.fixed ξ (-1) (by decide) ?_ Q.F Q.hF (fun i => hS _ (Ideal.subset_span ?_)) hF
    · intro a b hab u hu v hv hxu hxv
      by_cases ha : 0 ≤ a
      · rw [hnn a ha u hu hxu, zero_mul]
      · rw [hnn b (by omega) v hv hxv, mul_zero]
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩)))
  have h2 : ∀ f ∈ 𝒜 (-2), ξ f = 0 := by
    refine kill_part 𝒜 x hW.fixed ξ (-2) (by decide) ?_ Q.G Q.hG (fun i => hS _ (Ideal.subset_span ?_)) hG
    · intro a b hab u hu v hv hxu hxv
      by_cases ha : 0 ≤ a
      · rw [hnn a ha u hu hxu, zero_mul]
      · by_cases hb : 0 ≤ b
        · rw [hnn b hb v hv hxv, mul_zero]
        · obtain rfl : a = -1 := by omega
          rw [h1 u hu, zero_mul]
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))
  by_contra hn
  obtain ⟨f, hf, hne⟩ := (sign_holds O A 𝒜 x hW K ξ).1.1 hn
  exact hne (h2 f hf)
