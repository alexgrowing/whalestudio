import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegrallyClosedQuotientOfMemMinimalPrimes

open scoped TensorProduct

namespace GlobalTheory.BaseChangeComponents

variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]

noncomputable def incl (R : Subalgebra K Ω) : F ⊗[K] R →+* F ⊗[K] Ω :=
  (Algebra.TensorProduct.map (AlgHom.id K F) R.val).toRingHom

@[simp] theorem incl_tmul (R : Subalgebra K Ω) (a : F) (r : R) :
    incl F R (a ⊗ₜ r) = a ⊗ₜ (r : Ω) := rfl

theorem incl_injective (R : Subalgebra K Ω) : Function.Injective (incl F R) :=
  by
    intro x y hxy
    exact Module.Flat.lTensor_preserves_injective_linearMap (R := K) (M := F)
      R.val.toLinearMap Subtype.val_injective hxy

noncomputable def denoms (R : Subalgebra K Ω) : Submonoid (F ⊗[K] R) :=
  (nonZeroDivisors R).map (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := R))

theorem isLocalization_incl (R : Subalgebra K Ω)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) :
    @IsLocalization _ _ (denoms F R) (F ⊗[K] Ω) _ (incl F R).toAlgebra :=
  by
    letI := (incl F R).toAlgebra
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.1 hy
      have hr0 : (r : Ω) ≠ 0 := by
        have := nonZeroDivisors.ne_zero hr
        simpa using this
      have hval : algebraMap (F ⊗[K] R) (F ⊗[K] Ω)
          (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := R) r) =
            Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω) (r : Ω) := by
        show incl F R ((1 : F) ⊗ₜ r) = (1 : F) ⊗ₜ (r : Ω)
        exact incl_tmul F R 1 r
      rw [hval]
      exact (IsUnit.mk0 _ hr0).map _
    · intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨(0, 1), by simp⟩
      | tmul a w =>
        obtain ⟨c, hc, b, hb, hb0, hw⟩ := hR w
        have hbR : (⟨b, hb⟩ : R) ∈ nonZeroDivisors R :=
          mem_nonZeroDivisors_of_ne_zero (fun h => hb0 (congrArg Subtype.val h))
        refine ⟨(a ⊗ₜ ⟨c, hc⟩, ⟨(1 : F) ⊗ₜ ⟨b, hb⟩, Submonoid.mem_map_of_mem _ hbR⟩), ?_⟩
        show (a ⊗ₜ w) * incl F R ((1 : F) ⊗ₜ ⟨b, hb⟩) = incl F R (a ⊗ₜ ⟨c, hc⟩)
        rw [incl_tmul, incl_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        exact congrArg _ hw
      | add x y hx hy =>
        obtain ⟨⟨x₁, s₁⟩, h₁⟩ := hx
        obtain ⟨⟨x₂, s₂⟩, h₂⟩ := hy
        refine ⟨(x₁ * s₂ + x₂ * s₁, s₁ * s₂), ?_⟩
        simp only [Submonoid.coe_mul, map_mul, map_add] at h₁ h₂ ⊢
        linear_combination (algebraMap (F ⊗[K] R) (F ⊗[K] Ω) s₂) * h₁ +
          (algebraMap (F ⊗[K] R) (F ⊗[K] Ω) s₁) * h₂
    · intro x y h
      exact ⟨1, congrArg _ (incl_injective F R h)⟩

theorem minimalPrimes_eq (R : Subalgebra K Ω)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) :
    minimalPrimes (F ⊗[K] R) = Ideal.comap (incl F R) '' minimalPrimes (F ⊗[K] Ω) :=
  by
    letI := (incl F R).toAlgebra
    haveI := isLocalization_incl F R hR
    have h := IsLocalization.minimalPrimes_comap (denoms F R) (F ⊗[K] Ω) (⊥ : Ideal (F ⊗[K] Ω))
    have hb : Ideal.comap (algebraMap (F ⊗[K] R) (F ⊗[K] Ω)) ⊥ = ⊥ := by
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot _).1 (incl_injective F R)
    rw [hb] at h
    exact h

theorem isNoetherianRing_tensor (R : Subalgebra K Ω) (hfg : R.FG)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) : IsNoetherianRing (F ⊗[K] Ω) :=
  by
    letI := (incl F R).toAlgebra
    haveI := isLocalization_incl F R hR
    haveI : Algebra.FiniteType K R := (Subalgebra.fg_iff_finiteType R).1 hfg
    haveI : IsNoetherianRing (F ⊗[K] R) := Algebra.FiniteType.isNoetherianRing F (F ⊗[K] R)
    exact IsLocalization.isNoetherianRing (denoms F R) (F ⊗[K] Ω) inferInstance

theorem range_comp_incl {E : Type} [CommRing E] (R : Subalgebra K Ω) (g : F ⊗[K] Ω →+* E) :
    (g.comp (incl F R)).range = Subring.closure
      ((g.comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω)
        ∪ Set.range (g.comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))) :=
  by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Subring.zero_mem _
      | tmul a r =>
        have hsplit : (g.comp (incl F R)) (a ⊗ₜ r) =
            g (a ⊗ₜ (1 : Ω)) * g ((1 : F) ⊗ₜ (r : Ω)) := by
          rw [RingHom.comp_apply, incl_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
        rw [hsplit]
        exact Subring.mul_mem _ (Subring.subset_closure (Or.inr ⟨a, rfl⟩))
          (Subring.subset_closure (Or.inl ⟨r, r.2, rfl⟩))
      | add x y hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
    · rw [Subring.closure_le]
      rintro _ (⟨w, hw, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨(1 : F) ⊗ₜ ⟨w, hw⟩, by rw [RingHom.comp_apply, incl_tmul]; rfl⟩
      · exact ⟨a ⊗ₜ (1 : R), by rw [RingHom.comp_apply, incl_tmul]; rfl⟩

set_option maxHeartbeats 400000 in
private theorem closure_range_tensor_quotient_fraction (P : Ideal (F ⊗[K] Ω)) [P.IsPrime] :
    Subfield.closure (Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))) = ⊤ := by
  have key : ∀ s : (F ⊗[K] Ω), ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) s ∈
      Subfield.closure (Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subfield.zero_mem _
    | tmul a w =>
      have hsplit : ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (a ⊗ₜ w) =
          ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (a ⊗ₜ (1 : Ω)) * ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) ((1 : F) ⊗ₜ w) := by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplit]
      exact Subfield.mul_mem _ (Subfield.subset_closure (Or.inr ⟨a, rfl⟩))
        (Subfield.subset_closure (Or.inl ⟨w, rfl⟩))
    | add x y hx hy => rw [map_add]; exact Subfield.add_mem _ hx hy
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := (F ⊗[K] Ω) ⧸ P) z
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact Subfield.div_mem _ (key s) (key t)

set_option maxHeartbeats 400000 in
private theorem isIntegrallyClosed_closure_minimalPrime_quotient (R : Subalgebra K Ω) [Algebra.Smooth K R]
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a)
    (P : Ideal (F ⊗[K] Ω)) (hP : P ∈ minimalPrimes (F ⊗[K] Ω)) : IsIntegrallyClosed (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))))) := by
  have hker : RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)) = Ideal.comap (incl F R) P := by
    ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  let e := (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)).quotientKerEquivRange.trans
    (RingEquiv.subringCongr (range_comp_incl F R ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P))))
  have hmin : Ideal.comap (incl F R) P ∈ minimalPrimes (F ⊗[K] R) := by
    rw [minimalPrimes_eq F R hR]
    exact ⟨P, hP, rfl⟩
  haveI : IsIntegrallyClosed ((F ⊗[K] R) ⧸ RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R))) :=
    GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth F (F ⊗[K] R) _ (hker.symm ▸ hmin)
  exact IsIntegrallyClosed.of_equiv e

set_option maxHeartbeats 400000 in
private theorem exists_minimalPrime_closure_lift (R : Subalgebra K Ω)
    (hR : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a)
    (L : Type) [Field L] (χ : F →+* L) (ψ : R →+* L)
    (hχψ : ∀ a : K, ψ (algebraMap K R a) = χ (algebraMap K F a)) :
    ∃ (P : Ideal (F ⊗[K] Ω)) (_ : P ∈ minimalPrimes (F ⊗[K] Ω)) (φ : (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))))) →+* L),
      (∀ (r : R) (h : (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) r ∈ (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))), φ ⟨(((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) r, h⟩ = ψ r) ∧
      ∀ (a : F) (h : (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))) a ∈ (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))), φ ⟨(((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))) a, h⟩ = χ a := by
  letI : Algebra K L := (χ.comp (algebraMap K F)).toAlgebra
  let χ' : F →ₐ[K] L := { χ with commutes' := fun a => rfl }
  let ψ' : R →ₐ[K] L := { ψ with commutes' := fun a => hχψ a }
  let θ : F ⊗[K] R →ₐ[K] L := Algebra.TensorProduct.productMap χ' ψ'
  haveI : (RingHom.ker θ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal (F ⊗[K] R))) (J := RingHom.ker θ.toRingHom) bot_le
  have hq' : q ∈ minimalPrimes (F ⊗[K] R) := hq
  rw [minimalPrimes_eq F R hR] at hq'
  obtain ⟨P, hP, rfl⟩ := hq'
  have hker : RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)) = Ideal.comap (incl F R) P := by
    ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  let e := (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)).quotientKerEquivRange.trans
    (RingEquiv.subringCongr (range_comp_incl F R ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P))))
  have hlift : ∀ a ∈ RingHom.ker (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (incl F R)), θ.toRingHom a = 0 := by
    intro a ha
    rw [hker] at ha
    exact RingHom.mem_ker.1 (hqle ha)
  let φ := (Ideal.Quotient.lift _ θ.toRingHom hlift).comp e.symm.toRingHom
  have hφ : ∀ x, φ (e (Ideal.Quotient.mk _ x)) = θ x := by
    intro x
    simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
    rfl
  refine ⟨P, hP, φ, fun r h => ?_, fun a h => ?_⟩
  · have hpt : (⟨_, h⟩ : (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))) = e (Ideal.Quotient.mk _ ((1 : F) ⊗ₜ[K] r)) :=
      Subtype.ext (by
        show _ = ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (incl F R ((1 : F) ⊗ₜ[K] r))
        rw [incl_tmul]; rfl)
    rw [hpt, hφ]
    show χ 1 * ψ r = ψ r
    rw [map_one, one_mul]
  · have hpt : (⟨_, h⟩ : (Subring.closure ((((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω) ∪ Set.range (((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))))) = e (Ideal.Quotient.mk _ (a ⊗ₜ[K] (1 : R))) :=
      Subtype.ext (by
        show _ = ((algebraMap ((F ⊗[K] Ω) ⧸ P) (FractionRing ((F ⊗[K] Ω) ⧸ P))).comp (Ideal.Quotient.mk P)) (incl F R (a ⊗ₜ[K] (1 : R)))
        rw [incl_tmul]; rfl)
    rw [hpt, hφ]
    show χ a * ψ 1 = χ a
    rw [map_one, mul_one]

theorem components : ∀ (K F Ω : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω] (R₀ : Subalgebra K Ω), R₀.FG → (∀ x : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ x * b = a) → ∃ (J : Type) (_ : Finite J) (Ω' : J → Type) (_ : ∀ j, Field (Ω' j)) (α : ∀ j, Ω →+* Ω' j) (γ : ∀ j, F →+* Ω' j), (∀ j (a : K), α j (algebraMap K Ω a) = γ j (algebraMap K F a)) ∧ (∀ j, Subfield.closure (Set.range (α j) ∪ Set.range (γ j)) = ⊤) ∧ ∀ (R : Subalgebra K Ω), Algebra.Smooth K R → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) → (∀ j, IsIntegrallyClosed (Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j)))) ∧ ∀ (L : Type) [Field L] (χ : F →+* L) (ψ : R →+* L), (∀ a : K, ψ (algebraMap K R a) = χ (algebraMap K F a)) → ∃ (j : J) (φ : Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j)) →+* L), (∀ (r : R) (h : α j r ∈ Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j))), φ ⟨α j r, h⟩ = ψ r) ∧ ∀ (a : F) (h : γ j a ∈ Subring.closure (α j '' (R : Set Ω) ∪ Set.range (γ j))), φ ⟨γ j a, h⟩ = χ a :=
  by
    intro K F Ω _ _ _ _ _ R₀ hfg hR₀
    haveI := isNoetherianRing_tensor F R₀ hfg hR₀
    haveI hJ : Finite ↥(minimalPrimes (F ⊗[K] Ω)) :=
      (minimalPrimes.finite_of_isNoetherianRing (F ⊗[K] Ω)).to_subtype
    haveI hprime : ∀ j : ↥(minimalPrimes (F ⊗[K] Ω)), (j.1).IsPrime :=
      fun j => Ideal.minimalPrimes_isPrime j.2
    refine ⟨↥(minimalPrimes (F ⊗[K] Ω)), hJ, fun j => FractionRing ((F ⊗[K] Ω) ⧸ j.1),
      fun j => inferInstance, fun j => (((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)).comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom), fun j => (((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)).comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω))), ?_, ?_, ?_⟩
    · intro j a
      show ((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)) (Algebra.TensorProduct.includeRight (algebraMap K Ω a)) =
        ((algebraMap ((F ⊗[K] Ω) ⧸ j.1) (FractionRing ((F ⊗[K] Ω) ⧸ j.1))).comp (Ideal.Quotient.mk j.1)) ((algebraMap K F a) ⊗ₜ (1 : Ω))
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    · intro j
      exact closure_range_tensor_quotient_fraction F j.1
    · intro R _ hR
      refine ⟨fun j => isIntegrallyClosed_closure_minimalPrime_quotient F R hR j.1 j.2, fun L _ χ ψ hχψ => ?_⟩
      obtain ⟨P, hP, φ, h₁, h₂⟩ := exists_minimalPrime_closure_lift F R hR L χ ψ hχψ
      exact ⟨⟨P, hP⟩, φ, h₁, h₂⟩

end GlobalTheory.BaseChangeComponents
