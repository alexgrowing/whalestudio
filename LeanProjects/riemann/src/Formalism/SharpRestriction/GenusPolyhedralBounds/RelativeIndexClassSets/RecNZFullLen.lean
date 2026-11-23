import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.RecNZFullFacts

noncomputable section

namespace Formalism.MainNotions.Gaps.RN

open TensorProduct IsLocalRing IsDiscreteValuationRing

private theorem length_quot_span_singleton_dvr_lemma {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {ϖ ^ n}) = n := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
      Ideal.span_singleton_one]
  | succ n ih =>
    let f : (O ⧸ Ideal.span {ϖ}) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ (n + 1)}) :=
      (Ideal.span {ϖ}).mapQ (Ideal.span {ϖ ^ (n + 1)}) (LinearMap.mulLeft O (ϖ ^ n)) (by
        intro x hx
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
        refine Submodule.mem_comap.mpr (Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩)
        rw [LinearMap.mulLeft_apply]
        ring)
    let g : (O ⧸ Ideal.span {ϖ ^ (n + 1)}) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ n}) :=
      (Ideal.span {ϖ ^ (n + 1)}).mapQ (Ideal.span {ϖ ^ n}) LinearMap.id (by
        intro x hx
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
        refine Submodule.mem_comap.mpr (Ideal.mem_span_singleton'.mpr ⟨a * ϖ, ?_⟩)
        rw [LinearMap.id_apply]
        ring)
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (ϖ ^ n * x) = (0 : O ⧸ Ideal.span {ϖ ^ (n + 1)}) at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
      refine Ideal.mem_span_singleton'.mpr ⟨a, ?_⟩
      have hne : ϖ ^ n ≠ 0 := pow_ne_zero _ hϖ.ne_zero
      apply mul_left_cancel₀ hne
      rw [← ha]
      ring
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    have hex : Function.Exact f g := by
      intro y
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      change Submodule.Quotient.mk y = (0 : O ⧸ Ideal.span {ϖ ^ n}) ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hy
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
        refine ⟨Submodule.Quotient.mk a, ?_⟩
        change Submodule.Quotient.mk (ϖ ^ n * a) = (Submodule.Quotient.mk (a * ϖ ^ n) : O ⧸ Ideal.span {ϖ ^ (n + 1)})
        rw [mul_comm]
      · rintro ⟨x, hx⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        change Submodule.Quotient.mk (ϖ ^ n * x) = (Submodule.Quotient.mk y : O ⧸ Ideal.span {ϖ ^ (n + 1)}) at hx
        rw [Submodule.Quotient.eq] at hx
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hx
        refine Ideal.mem_span_singleton'.mpr ⟨x - b * ϖ, ?_⟩
        linear_combination -hb
    have hs : Module.length O (O ⧸ Ideal.span {ϖ}) = 1 := by
      have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := by
        first
          | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
          | exact hϖ.maximalIdeal_eq
      rw [Module.length_eq_one_iff, ← hm]
      first
        | exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal O).out
        | exact isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal O))
        | infer_instance
    rw [Module.length_eq_add_of_exact f g hf hg hex, hs, ih]
    push_cast
    ring

theorem length_quot_span_singleton_dvr {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O)
    (ht : t ≠ 0) : Module.length O (O ⧸ Ideal.span {t}) = addVal O t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ n rfl, Ideal.span_singleton_mul_left_unit u.isUnit]
  exact length_quot_span_singleton_dvr_lemma ϖ hϖ n

open Classical in

theorem length_pi_span_quot (A O : Type*) [CommRing A] [CommRing O] [Algebra A O] (ι : Type*) [Fintype ι]
    (N : Submodule A (ι → A)) :
    Module.length O ((ι → O) ⧸ Submodule.span O ((fun x : ι → A => algebraMap A O ∘ x) '' (N : Set (ι → A)))) =
      Module.length O (O ⊗[A] ((ι → A) ⧸ N)) := by
  set S := Submodule.span O ((fun x : ι → A => algebraMap A O ∘ x) '' (N : Set (ι → A))) with hS

  let Φ : (ι → O) →ₗ[O] O ⊗[A] ((ι → A) ⧸ N) :=
    { toFun := fun v => ∑ i, v i ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N)
      map_add' := fun v w => by
        simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, TensorProduct.smul_tmul'] }
  have hmk : ∀ x : ι → A, (Submodule.Quotient.mk x : (ι → A) ⧸ N) =
      ∑ i, x i • (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N) := by
    intro x
    have hx : x = ∑ i, x i • Pi.single i (1 : A) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [← Submodule.mkQ_apply, map_sum, map_smul]
  have hΦg : ∀ x : ι → A, Φ (algebraMap A O ∘ x) = (1 : O) ⊗ₜ[A] (Submodule.Quotient.mk x : (ι → A) ⧸ N) := by
    intro x
    change ∑ i, algebraMap A O (x i) ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N) = _
    rw [hmk x, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hker : S ≤ LinearMap.ker Φ := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hx0 : (Submodule.Quotient.mk x : (ι → A) ⧸ N) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hx
    show Φ (algebraMap A O ∘ x) = 0
    rw [hΦg x, hx0, TensorProduct.tmul_zero]
  let Φbar : ((ι → O) ⧸ S) →ₗ[O] O ⊗[A] ((ι → A) ⧸ N) := S.liftQ Φ hker
  let ψ1 : (ι → A) →ₗ[A] (ι → O) ⧸ S :=
    (S.mkQ.restrictScalars A) ∘ₗ (LinearMap.compLeft (Algebra.linearMap A O) ι)
  have hN : N ≤ LinearMap.ker ψ1 := by
    intro x hx
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (algebraMap A O ∘ x) : (ι → O) ⧸ S) = 0
    rw [Submodule.Quotient.mk_eq_zero, hS]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  let ψ0 : ((ι → A) ⧸ N) →ₗ[A] (ι → O) ⧸ S := N.liftQ ψ1 hN
  let Ψ : O ⊗[A] ((ι → A) ⧸ N) →ₗ[O] (ι → O) ⧸ S :=
    TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton O (((ι → A) ⧸ N) →ₗ[A] (ι → O) ⧸ S) ψ0)
  have h1 : Φbar ∘ₗ Ψ = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.AlgebraTensorModule.lift_tmul,
      LinearMap.toSpanSingleton_apply, LinearMap.smul_apply, Submodule.liftQ_apply, map_smul]
    change c • Φ (algebraMap A O ∘ x) = _
    rw [hΦg x, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hs : ∀ i : ι, algebraMap A O ∘ (Pi.single i (1 : A) : ι → A) = Pi.single i (1 : O) := by
    intro i
    ext k
    by_cases h : k = i <;> simp [Pi.single_apply, h]
  have h2 : Ψ ∘ₗ Φbar = LinearMap.id := by
    apply Submodule.linearMap_qext
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
    change Ψ (∑ i, v i ⊗ₜ[A] (Submodule.Quotient.mk (Pi.single i 1) : (ι → A) ⧸ N)) = _
    rw [map_sum]
    simp only [Ψ, TensorProduct.AlgebraTensorModule.lift_tmul, LinearMap.toSpanSingleton_apply,
      LinearMap.smul_apply, Submodule.liftQ_apply]
    change ∑ i, v i • (Submodule.Quotient.mk (algebraMap A O ∘ Pi.single i 1) : (ι → O) ⧸ S) = _
    have hv : v = ∑ i, v i • Pi.single i (1 : O) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    rw [← Submodule.mkQ_apply, map_sum]
    simp only [map_smul, Submodule.mkQ_apply, hs]
  exact LinearEquiv.length_eq (LinearEquiv.ofLinear Φbar Ψ h1 h2)

theorem lenBaseChangeDVR : LenBaseChangeDVR := by
  intro A O _ _ _ _ _ _ f hloc hinj ϖ hϖ ι _ N
  letI : Algebra A O := f.toAlgebra
  haveI : IsLocalHom (algebraMap A O) := hloc
  haveI : Module.IsTorsionFree A O := Module.IsTorsionFree.of_smul_eq_zero (fun a c h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left (fun h0 => hinj (h0.trans (map_zero f).symm)))
  haveI : Module.Flat A O := inferInstance
  have h0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (h.trans (map_zero f).symm))
  have h1 := length_pi_span_quot A O ι N
  have h2 : (IsLocalRing.maximalIdeal A).map (algebraMap A O) = Ideal.span {f ϖ} := by
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    rfl
  have h3 : ((addVal O (f ϖ)).toNat : ℕ∞) = addVal O (f ϖ) :=
    ENat.coe_toNat (fun h => h0 (addVal_eq_top_iff.1 h))
  rw [IsLocalRing.length_baseChange, h2, length_quot_span_singleton_dvr _ h0] at h1
  rw [h3, mul_comm]
  exact h1

end Formalism.MainNotions.Gaps.RN

end
