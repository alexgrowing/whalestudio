import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SliceHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FgHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SignHolds

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.fin_gen {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (ξ : A →ₐ[O] K) (j : ℤ) (s : Finset A)
    (hs : Submodule.span (𝒜 0) (s : Set A) = oz 𝒜 j) (h : ∃ f ∈ 𝒜 j, ξ f ≠ 0) : ∃ f ∈ s, ξ f ≠ 0 := by
  obtain ⟨f, hf, hξ⟩ := h
  by_contra hne
  push_neg at hne
  have hf' : f ∈ Submodule.span (𝒜 0) (s : Set A) := by
    rw [hs]
    exact (mem_oz 𝒜).2 hf
  apply hξ
  clear hξ hf
  induction hf' using Submodule.span_induction with
  | mem y hy => exact hne y hy
  | zero => exact map_zero ξ
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul a y _ hy => rw [Algebra.smul_def, map_mul, hy, mul_zero]

private theorem UpperTheory.V.Alg.M.fin_act {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (t : Kˣ) (ξ : A →ₐ[O] K) {j : ℤ} {a : A}
    (ha : a ∈ 𝒜 j) : act 𝒜 (tz t) ξ a = ((t ^ j : Kˣ) : K) * ξ a := act_of_mem 𝒜 _ ξ ha

private theorem UpperTheory.V.Alg.M.fin_inv {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (t : Kˣ) (ξ : A →ₐ[O] K) :
    ξ = act 𝒜 (tz t⁻¹) (act 𝒜 (tz t) ξ) := by
  classical
  ext a
  rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm := SetLike.coe_mem (DirectSum.decompose 𝒜 a i)
  rw [fin_act 𝒜 t⁻¹ _ hm, fin_act 𝒜 t ξ hm, ← mul_assoc, ← Units.val_mul, ← mul_zpow, inv_mul_cancel,
    one_zpow, Units.val_one, one_mul]

private theorem UpperTheory.V.Alg.M.fin_onS {O A K : Type} [CommRing O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (t : Kˣ) (ξ : A →ₐ[O] K) (I : Ideal A)
    (hI : I.IsHomogeneous 𝒜) (h : OnS I ξ) : OnS I (act 𝒜 (tz t) ξ) := by
  classical
  intro f hf
  rw [← DirectSum.sum_support_decompose 𝒜 f, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [fin_act 𝒜 _ _ (DirectSum.decompose 𝒜 f j).2, h _ (hI j hf), mul_zero]

theorem UpperTheory.V.Alg.M.fin_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ I : Ideal A, I.IsHomogeneous 𝒜 → M2 𝒜 I → M4 𝒜 K I → ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hx I hI h2 h4
  obtain ⟨s, hs⟩ := fg_holds O A 𝒜 x hx (-2)
  obtain ⟨s', hs'⟩ := fg_holds O A 𝒜 x hx 2
  have hsm : ∀ f ∈ s, f ∈ 𝒜 (-2) := by
    intro f hf
    rw [← mem_oz 𝒜, ← hs]
    exact Submodule.subset_span hf
  have hsm' : ∀ g ∈ s', g ∈ 𝒜 2 := by
    intro g hg
    rw [← mem_oz 𝒜, ← hs']
    exact Submodule.subset_span hg
  let S : Set (A →ₐ[O] K) := ⋃ f ∈ (s : Set A), ⋃ g ∈ (s' : Set A),
    {ξ | OnS I ξ ∧ ξ f = 1 ∧ ξ g ≠ 0 ∧ TwoSigned 𝒜 ξ}
  have hS : S.Finite := by
    refine s.finite_toSet.biUnion fun f hf => s'.finite_toSet.biUnion fun g hg => ?_
    exact (slice_holds O K A 𝒜 x hx I hI h2 h4 f (hsm f hf) g (hsm' g hg)).1.subset
      fun ξ hξ => ⟨hξ.1, hξ.2.1, hξ.2.2.1⟩
  refine ⟨hS.toFinset, fun ξ hξ => ?_, fun ξ hon htw => ?_⟩
  · rw [Set.Finite.mem_toFinset] at hξ
    simp only [S, Set.mem_iUnion, Set.mem_setOf_eq] at hξ
    obtain ⟨f, -, g, -, h1, -, -, h3⟩ := hξ
    exact ⟨h1, h3⟩
  · obtain ⟨f0, hf0, hξf0⟩ := (sign_holds O A 𝒜 x hx K ξ).1.1 htw.1
    obtain ⟨g0, hg0, hξg0⟩ := (sign_holds O A 𝒜 x hx K ξ).2.1 htw.2
    obtain ⟨f, hf, hξf⟩ := fin_gen 𝒜 ξ (-2) s hs ⟨f0, hf0, hξf0⟩
    obtain ⟨g, hg, hξg⟩ := fin_gen 𝒜 ξ 2 s' hs' ⟨g0, hg0, hξg0⟩
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (ξ f) (by norm_num : 0 < 2)
    have hr0 : r ≠ 0 := by
      rintro rfl
      apply hξf
      rw [← hr]
      ring
    have e1 : act 𝒜 (tz (Units.mk0 r hr0)) ξ f = 1 := by
      rw [fin_act 𝒜 _ ξ (hsm f hf), ← hr, Units.val_zpow_eq_zpow_val, Units.val_mk0, zpow_neg, zpow_ofNat,
        inv_mul_cancel₀ (pow_ne_zero _ hr0)]
    have e2 : act 𝒜 (tz (Units.mk0 r hr0)) ξ g ≠ 0 := by
      rw [fin_act 𝒜 _ ξ (hsm' g hg)]
      exact mul_ne_zero (Units.ne_zero _) hξg
    have e3 : TwoSigned 𝒜 (act 𝒜 (tz (Units.mk0 r hr0)) ξ) :=
      ⟨(sign_holds O A 𝒜 x hx K _).1.2 ⟨f, hsm f hf, by rw [e1]; exact one_ne_zero⟩,
        (sign_holds O A 𝒜 x hx K _).2.2 ⟨g, hsm' g hg, e2⟩⟩
    refine ⟨act 𝒜 (tz (Units.mk0 r hr0)) ξ, ?_, (Units.mk0 r hr0)⁻¹, fin_inv 𝒜 _ ξ⟩
    rw [Set.Finite.mem_toFinset]
    simp only [S, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨f, hf, g, hg, fin_onS 𝒜 _ ξ I hI hon, e1, e2, e3⟩
