import Mathlib

set_option linter.style.haveILetI false

noncomputable section
open ValuativeRel IsDedekindDomain

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace PI.LocDualGen.EpF

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CharZero K]

local notation "C" => integralClosure 𝒪[K] L

theorem tf : Module.IsTorsionFree 𝒪[K] L := by
  first
    | exact Module.IsTorsionFree.trans_faithfulSMul 𝒪[K] K L
    | (rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective,
        IsScalarTower.algebraMap_eq 𝒪[K] K L]
       exact (algebraMap K L).injective.comp Subtype.val_injective)

theorem dd : IsDedekindDomain C := integralClosure.isDedekindDomain 𝒪[K] K L
theorem fr : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
theorem mf : Module.Finite 𝒪[K] C := IsIntegralClosure.finite 𝒪[K] K L C
theorem tfC : Module.IsTorsionFree 𝒪[K] C := by
  have hf : FaithfulSMul 𝒪[K] L := Module.isTorsionFree_iff_faithfulSMul.1 (tf K L)
  rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective]
  intro a b h
  have h' := congrArg (algebraMap C L) h
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h'
  exact (FaithfulSMul.algebraMap_injective 𝒪[K] L) h'

attribute [local instance] dd fr mf tfC

theorem sepFR : Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing C) := by
  first
    | infer_instance
    | exact Algebra.IsAlgebraic.isSeparable_of_perfectField

attribute [local instance] sepFR

theorem differentIdeal_eq_top
    (hU : ∀ x : C, x * x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] →
      x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) :
    differentIdeal 𝒪[K] C = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI := hPmax.isPrime
  have hdvd := (dvd_differentIdeal_iff (A := 𝒪[K]) (B := C) (P := P)).1 (Ideal.dvd_iff_le.2 hle)
  apply hdvd
  have hpmax : (P.comap (algebraMap 𝒪[K] C)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hpeq : P.comap (algebraMap 𝒪[K] C) = 𝓂[K] := IsLocalRing.eq_maximalIdeal hpmax
  haveI : P.LiesOver 𝓂[K] := ⟨hpeq.symm⟩
  letI := Localization.AtPrime.instAlgebraOfLiesOver 𝓂[K] P
  haveI : Localization.AtPrime.IsLiesOverAlgebra 𝓂[K] P :=
    Localization.AtPrime.instIsLiesOverAlgebra 𝓂[K] P
  rw [Algebra.isUnramifiedAt_iff_map_eq 𝒪[K] 𝓂[K] P]
  refine ⟨?_, ?_⟩
  · haveI : Finite (𝒪[K] ⧸ 𝓂[K]) := (inferInstance : Finite 𝓀[K])
    haveI : Finite 𝓂[K].ResidueField :=
      Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField 𝓂[K]).2
    haveI : PerfectField 𝓂[K].ResidueField := inferInstance
    haveI : Algebra.IsAlgebraic 𝓂[K].ResidueField P.ResidueField := inferInstance
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  · have hP0 : P ≠ ⊥ := fun h =>
      differentIdeal_ne_bot (A := 𝒪[K]) (B := C) (le_bot_iff.1 (h ▸ hle))
    haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hP0 (Localization.AtPrime P)
    haveI : FaithfulSMul 𝒪[K] C := Module.isTorsionFree_iff_faithfulSMul.1 (tfC K L)
    have hinj : Function.Injective (algebraMap C (Localization.AtPrime P)) :=
      IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
    have hinjO : Function.Injective (algebraMap 𝒪[K] (Localization.AtPrime P)) := by
      rw [IsScalarTower.algebraMap_eq 𝒪[K] C (Localization.AtPrime P)]
      exact hinj.comp (FaithfulSMul.algebraMap_injective 𝒪[K] C)
    have hmap : Ideal.map (algebraMap 𝒪[K] (Localization.AtPrime P)) 𝓂[K] =
        Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    have hJP : Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] ≤ P := Ideal.map_le_iff_le_comap.2 hpeq.ge
    have hIle : Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hJP
    have hI0 : Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) ≠ ⊥ := by
      rw [← hmap, Ne, Ideal.map_eq_bot_iff_of_injective hinjO]
      exact IsDiscreteValuationRing.not_a_field _
    have hrad : ∀ x : (Localization.AtPrime P), x * x ∈ Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) →
        x ∈ Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
      intro x hx
      obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
      have h1 : algebraMap C (Localization.AtPrime P) (c * c) ∈
          Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
        have he : algebraMap C (Localization.AtPrime P) (c * c) = (IsLocalization.mk' (Localization.AtPrime P) c s * IsLocalization.mk' (Localization.AtPrime P) c s) *
            algebraMap C (Localization.AtPrime P) ((s * s : P.primeCompl) : C) := by
          rw [← IsLocalization.mk'_mul, IsLocalization.mk'_spec]
        rw [he]
        exact Ideal.mul_mem_right _ _ hx
      obtain ⟨⟨⟨a, ha⟩, ⟨m, hm⟩⟩, he⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)).1 h1
      have h2 : c * c * m = a := hinj (by rw [map_mul]; exact he)
      have h3 : (m * c) * (m * c) ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] := by
        have hr : (m * c) * (m * c) = m * (c * c * m) := by ring
        rw [hr, h2]
        exact Ideal.mul_mem_left _ _ ha
      have h4 := hU _ h3
      have hv : IsUnit (algebraMap C (Localization.AtPrime P) (m * s)) :=
        IsLocalization.map_units (Localization.AtPrime P) (⟨m, hm⟩ * s : P.primeCompl)
      refine (Ideal.unit_mul_mem_iff_mem _ hv).1 ?_
      have h6 : algebraMap C (Localization.AtPrime P) (m * s) * IsLocalization.mk' (Localization.AtPrime P) c s = algebraMap C (Localization.AtPrime P) (m * c) := by
        rw [map_mul, mul_assoc, IsLocalization.mk'_spec', ← map_mul]
      rw [h6]
      exact Ideal.mem_map_of_mem _ h4
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI0 hϖ
    rw [hmap]
    apply le_antisymm hIle
    rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    have key : ∀ j : ℕ, ϖ ^ (j + 1) ∈ Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) →
        ϖ ∈ Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        intro hj
        rcases Nat.eq_zero_or_pos j with rfl | hpos
        · simpa using hj
        · have hh : ϖ ^ ((j + 2) / 2) * ϖ ^ ((j + 2) / 2) ∈
              Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
            rw [← pow_add]
            have hs : (j + 2) / 2 + (j + 2) / 2 = (j + 1) + ((j + 2) / 2 + (j + 2) / 2 - (j + 1)) := by
              omega
            rw [hs, pow_add]
            exact Ideal.mul_mem_right _ _ hj
          have h2 := hrad _ hh
          have hs : (j + 2) / 2 = ((j + 2) / 2 - 1) + 1 := by omega
          rw [hs] at h2
          exact ih _ (by omega) h2
    cases n with
    | zero =>
      exfalso
      have h1 : (1 : (Localization.AtPrime P)) ∈ Ideal.map (algebraMap C (Localization.AtPrime P)) (Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) := by
        rw [hn]
        simp
      exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime P)).ne_top ((Ideal.eq_top_iff_one _).2 (hIle h1))
    | succ k =>
      exact key k (by rw [hn]; exact Ideal.mem_span_singleton_self _)

theorem mem_C_iff (x : L) : x ∈ (1 : FractionalIdeal (nonZeroDivisors C) L) ↔ x ∈ C := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem selfDual_field
    (hU : ∀ x : C, x * x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K] →
      x ∈ Ideal.map (algebraMap 𝒪[K] C) 𝓂[K]) (x : L) :
    (∀ y ∈ C, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ C := by
  have hdual : FractionalIdeal.dual 𝒪[K] K (1 : FractionalIdeal (nonZeroDivisors C) L) = 1 := by
    have h := coeIdeal_differentIdeal 𝒪[K] K L C
    rw [differentIdeal_eq_top K L hU, FractionalIdeal.coeIdeal_top] at h
    exact inv_eq_one.1 h.symm
  have hr : ∀ z : K, z ∈ (algebraMap 𝒪[K] K).range ↔ z ∈ 𝒪[K] :=
    fun z => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
  have h10 : (1 : FractionalIdeal (nonZeroDivisors C) L) ≠ 0 := by
    rw [Ne, ← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_eq_zero]
    exact top_ne_bot
  rw [← mem_C_iff K L x, ← hdual, FractionalIdeal.mem_dual h10]
  simp only [Algebra.traceForm_apply, mem_C_iff K L, hr]

end PI.LocDualGen.EpF
