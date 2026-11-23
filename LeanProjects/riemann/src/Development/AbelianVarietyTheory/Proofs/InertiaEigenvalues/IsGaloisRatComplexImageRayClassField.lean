import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsGaloisOfIsRayFieldTop

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.RayTopGalois GlobalTheory.FieldSize

namespace GlobalTheory.RayNatGalois

theorem isModulus_transport {K K' N : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field N]
    [NumberField N] [Algebra K N] [Algebra K' N] (s : K ≃+* K')
    (hs : ∀ x, algebraMap K' N (s x) = algebraMap K N x) [IsGalois K N] [IsGalois K' N] {𝔪 : Ideal (𝓞 K)}
    {𝔪' : Ideal (𝓞 K')} (hm' : 𝔪' ≠ ⊥) (hmm : ∀ x, RingOfIntegers.mapRingEquiv s x ∈ 𝔪' ↔ x ∈ 𝔪)
    (h : ∀ χ : (N ≃ₐ[K] N) →* ℂˣ, IsModulus N χ 𝔪) (χ : (N ≃ₐ[K'] N) →* ℂˣ) : IsModulus N χ 𝔪' := by
  have hc : ∀ a : 𝓞 K, IsCoprime (Ideal.span {RingOfIntegers.mapRingEquiv s a}) 𝔪' →
      IsCoprime (Ideal.span {a}) 𝔪 := fun a H => by
    rw [Ideal.isCoprime_iff_exists] at H ⊢
    obtain ⟨i, hi, j, hj, hij⟩ := H
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
    obtain ⟨c, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective c
    obtain ⟨j, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective j
    refine ⟨c * a, Ideal.mem_span_singleton'.2 ⟨c, rfl⟩, j, (hmm j).1 hj,
      (RingOfIntegers.mapRingEquiv s).injective ?_⟩
    rw [map_add, map_mul, hij, map_one]
  refine ⟨hm', fun 𝔭 hp => ?_, fun α β hr => ?_⟩
  · obtain ⟨𝔮, rfl⟩ := (primeEquiv s).surjective 𝔭
    rw [heckeVal_transport s hs]
    refine (h _).2.1 𝔮 fun H => hp (Ideal.dvd_iff_le.2 fun x hx => ?_)
    obtain ⟨y, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective x
    change (RingOfIntegers.mapRingEquiv s).symm (RingOfIntegers.mapRingEquiv s y) ∈ 𝔮.asIdeal
    rw [RingEquiv.symm_apply_apply]
    exact Ideal.le_of_dvd H ((hmm y).1 hx)
  · obtain ⟨a, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective α
    obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective β
    have ha : a ≠ 0 := fun h => hr.1 (by rw [h, map_zero])
    have hb : b ≠ 0 := fun h => hr.2.1 (by rw [h, map_zero])
    rw [heckeIdeal_transport s hs χ ha, heckeIdeal_transport s hs χ hb]
    refine (h _).2.2 a b ⟨ha, hb, hc _ hr.2.2.1, hc _ hr.2.2.2.1, (hmm _).1 ?_, fun φ => ?_⟩
    · rw [map_sub]; exact hr.2.2.2.2.1
    · have := hr.2.2.2.2.2 (φ.comp s.symm.toRingHom)
      change 0 < φ (s.symm (s a)) * φ (s.symm (s b)) at this
      rwa [s.symm_apply_apply, s.symm_apply_apply] at this

theorem exists_extension {L N : Type} [Field L] [NumberField L] [Field N] [NumberField N] [i : Algebra L N]
    [hab : IsAbelianGalois L N] {n : ℕ} (hn : n ≠ 0) (h : IsRay N (Ideal.span {(n : 𝓞 L)})) (s : L ≃+* L) :
    ∃ f : N →+* N, ∀ x, f (algebraMap L N x) = algebraMap L N (s x) := by
  have hb : Ideal.span {(n : 𝓞 L)} ≠ ⊥ := by simpa using hn
  have hmm : ∀ x, RingOfIntegers.mapRingEquiv s x ∈ Ideal.span {(n : 𝓞 L)} ↔ x ∈ Ideal.span {(n : 𝓞 L)} :=
    fun x => by
      rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton,
        ← map_dvd_iff (RingOfIntegers.mapRingEquiv s) (a := (n : 𝓞 L)) (b := x), map_natCast]
  let j : Algebra L N := ((@algebraMap L N _ _ i).comp s.symm.toRingHom).toAlgebra
  have hs : ∀ x, @algebraMap L N _ _ j (s x) = @algebraMap L N _ _ i x := fun x =>
    congrArg (@algebraMap L N _ _ i) (s.symm_apply_apply x)
  have hab' := @isAbelianGalois_transport L L N _ _ _ _ i j s hs _ hab
  have hm := @GlobalTheory.RayMaximal.isModulus_of_isRay L _ _ N _ _ i hab _ _ h dvd_rfl hb
  obtain ⟨f⟩ := @rayClassFieldMaximalSt_holds L N N _ _ _ _ i hab _ _ j hab' _ hb h
    (@isModulus_transport L L N _ _ _ _ _ _ i j s hs (@IsAbelianGalois.toIsGalois _ _ _ _ i hab)
      (@IsAbelianGalois.toIsGalois _ _ _ _ j hab') _ _ hb hmm hm)
  refine ⟨@AlgHom.toRingHom L N N _ _ _ j i f, fun x => ?_⟩
  rw [← hs]
  exact @AlgHom.commutes L N N _ _ _ j i f (s x)

theorem isGalois_of_isRay_nat (K : Type) {L N : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field N]
    [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L]
    [IsAbelianGalois L N] {n : ℕ} (hn : n ≠ 0) (h : IsRay N (Ideal.span {(n : 𝓞 L)})) : IsGalois K N := by
  refine IsGalois.of_fixedField_eq_bot K N (eq_bot_iff.2 fun x hx => ?_)
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) x).2 fun σ =>
    hx (σ.restrictScalars K) trivial
  obtain ⟨z, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) y).2 fun s => by
    obtain ⟨f, hf⟩ := exists_extension hn h s.toRingEquiv
    let g : N →ₐ[K] N := { f with
      commutes' := fun k => by
        rw [IsScalarTower.algebraMap_apply K L N]
        exact (hf _).trans (congrArg _ (s.commutes k)) }
    exact (algebraMap L N).injective ((hf y).symm.trans
      (hx (AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g)) trivial))
  rw [← IsScalarTower.algebraMap_apply]
  exact IntermediateField.algebraMap_mem _ z

theorem isGalois_fieldRange : ∀ {K H : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) →
    ∀ j : H →+* ℂ, IsGalois ℚ j.toRatAlgHom.fieldRange := by
  intro K H _ _ _ _ _ _ _ n hn h j
  have : IsGalois ℚ H := isGalois_of_isRay_nat ℚ hn h
  exact IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField j.toRatAlgHom)

end GlobalTheory.RayNatGalois

end
