import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero

open TensorProduct

namespace GlobalTheory.DVRBaseChange

theorem exists_dvr_quotient (W : Type) [CommRing W] [IsLocalRing W] (π : W)
    (hm : IsLocalRing.maximalIdeal W = Ideal.span {π}) (hπ : ¬ IsNilpotent π) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (q : W →+* V), Irreducible (q π) := by
  classical
  have hnu : ∀ x : W, ¬ IsUnit x ↔ π ∣ x := fun x => by
    rw [← Ideal.mem_span_singleton, ← hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  let J : Ideal W := ⨅ n : ℕ, Ideal.span {π ^ n}
  have hJ : ∀ x, x ∈ J ↔ ∀ n : ℕ, π ^ n ∣ x := fun x => by
    simp only [J, Ideal.mem_iInf, Ideal.mem_span_singleton]
  have hpow : ∀ n : ℕ, π ^ n ∉ J := by
    intro n hn
    obtain ⟨y, hy⟩ := (hJ _).1 hn (n + 1)
    have hu : IsUnit (1 - π * y) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((hnu _).2 (dvd_mul_right _ _))
    refine hπ ⟨n, ?_⟩
    have : π ^ n * (1 - π * y) = 0 := by linear_combination hy
    exact (hu.mul_left_eq_zero).1 this
  have hfac : ∀ x, x ∉ J → ∃ (n : ℕ) (u : W), IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra hc
      push Not at hc
      exact hx ((hJ x).2 fun n => (pow_dvd_pow π (Nat.le_succ n)).trans (hc n))
    have h1 : π ^ (Nat.find hex) ∣ x := by
      rcases h : Nat.find hex with _ | m
      · simp
      · by_contra hc
        exact Nat.find_min hex (m := m) (by omega) hc
    obtain ⟨u, hu⟩ := h1
    refine ⟨_, u, ?_, hu⟩
    by_contra hc
    obtain ⟨v, rfl⟩ := (hnu u).1 hc
    exact Nat.find_spec hex ⟨v, hu.trans (by ring)⟩
  have hprime : J.IsPrime := by
    refine ⟨fun h => hpow 0 (h ▸ Submodule.mem_top), fun {x y} hxy => ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨n, u, hu, rfl⟩ := hfac x hc.1
    obtain ⟨m, v, hv, rfl⟩ := hfac y hc.2
    refine hpow (n + m) ?_
    rw [← J.mul_unit_mem_iff_mem (hu.mul hv)]
    convert hxy using 1
    ring
  have hdom : IsDomain (W ⧸ J) := Ideal.Quotient.isDomain J
  have hloc : IsLocalRing (W ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hirr : Irreducible (Ideal.Quotient.mk J π) := by
    refine IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ ?_ ?_
    · rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      simpa using hpow 1
    · rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
        Ideal.Quotient.mk_surjective, hm, Ideal.map_span, Set.image_singleton]
  refine ⟨W ⧸ J, inferInstance, hdom,
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, ?_⟩,
    Ideal.Quotient.mk J, hirr⟩
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, u, hu, rfl⟩ := hfac x (fun h => hx (Ideal.Quotient.eq_zero_iff_mem.2 h))
  refine ⟨n, ?_⟩
  rw [map_mul, map_pow]
  exact associated_mul_unit_right _ _ (hu.map _)

theorem exists_dvr_of_isRadical (S : Type) [CommRing S] (π : S)
    (hrad : (Ideal.span {π}).IsRadical) (hne : Ideal.span {π} ≠ ⊤)
    (hreg : ∀ s, π * s = 0 → s = 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (q : S →+* V), Irreducible (q π) := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  have hpp : p.IsPrime := hp.1.1
  let W := Localization.AtPrime p
  have hm : IsLocalRing.maximalIdeal W = Ideal.span {algebraMap S W π} := by
    have h1 := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes W p _ hp
    rw [← IsLocalization.map_radical p.primeCompl, hrad.radical,
      Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton] at h1
    exact h1.symm
  have hn : ¬ IsNilpotent (algebraMap S W π) := by
    rintro ⟨n, hn⟩
    rw [← map_pow, IsLocalization.map_eq_zero_iff p.primeCompl] at hn
    obtain ⟨⟨s, hs⟩, h⟩ := hn
    have key : ∀ (n : ℕ) (s : S), s * π ^ n = 0 → s = 0 := by
      intro n
      induction n with
      | zero => intro s h; simpa using h
      | succ n ih => intro s h; exact ih s (hreg _ (by linear_combination h))
    exact hs (by rw [key n s h]; exact p.zero_mem)
  obtain ⟨V, i1, i2, i3, q, hq⟩ := exists_dvr_quotient W _ hm hn
  exact ⟨V, i1, i2, i3, q.comp (algebraMap S W), hq⟩

theorem exists_unramified_extension :
    ∀ (K F T : Type) [Field K] [CharZero K] [Field F] [Algebra K F] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Algebra K T], ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (i : T →+* V) (χ : F →+* V), Function.Injective i ∧ (∀ ϖ : T, Irreducible ϖ → Irreducible (i ϖ)) ∧ IsLocalHom i ∧ ∀ a : K, i (algebraMap K T a) = χ (algebraMap K F a) := by
  intro K F T _ _ _ _ _ _ _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  let m := IsLocalRing.maximalIdeal T
  have hm : m = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  letI : Field (T ⧸ m) := Ideal.Quotient.field m
  let g : T ⊗[K] F →ₐ[K] (T ⧸ m) ⊗[K] F :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K m) (AlgHom.id K F)
  have hker : RingHom.ker g = Ideal.span {ϖ ⊗ₜ[K] (1 : F)} := by
    rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective K m)]
    have : RingHom.ker (Ideal.Quotient.mkₐ K m) = Ideal.span {ϖ} := by
      rw [← hm]; exact Ideal.mk_ker
    rw [this, Ideal.map_span, Set.image_singleton]
    rfl
  have hred : IsReduced ((T ⧸ m) ⊗[K] F) := GlobalTheory.ReducedAlg.isReduced_field_tensor _ _
  have hrad : (Ideal.span {ϖ ⊗ₜ[K] (1 : F)}).IsRadical := by
    rw [← hker]
    exact Ideal.isRadical_bot.comap _
  have hne : Ideal.span {ϖ ⊗ₜ[K] (1 : F)} ≠ ⊤ := by
    rw [← hker]
    exact RingHom.ker_ne_top _
  have hreg : ∀ s : T ⊗[K] F, (ϖ ⊗ₜ[K] (1 : F)) * s = 0 → s = 0 := by
    intro s hs
    have hinj : Function.Injective ((LinearMap.mulLeft K ϖ).rTensor F) :=
      Module.Flat.rTensor_preserves_injective_linearMap _
        (fun a b h => mul_left_cancel₀ hϖ.ne_zero h)
    have key : ∀ s : T ⊗[K] F, (LinearMap.mulLeft K ϖ).rTensor F s = (ϖ ⊗ₜ[K] (1 : F)) * s := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add, hx, hy, mul_add]
    exact hinj (by rw [key, hs, map_zero])
  obtain ⟨V, i1, i2, i3, q, hq⟩ := exists_dvr_of_isRadical _ _ hrad hne hreg
  let i : T →+* V := q.comp Algebra.TensorProduct.includeLeftRingHom
  have hi : Irreducible (i ϖ) := hq
  refine ⟨V, i1, i2, i3, i, q.comp (Algebra.TensorProduct.includeRight (R := K) (A := T)).toRingHom,
    ?_, ?_, ⟨?_⟩, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [map_mul, map_pow] at hx
    exact mul_ne_zero (u.isUnit.map i).ne_zero (pow_ne_zero n hi.ne_zero) hx
  · intro ϖ' h'
    exact ((IsDiscreteValuationRing.associated_of_irreducible T hϖ h').map i).irreducible hi
  · intro x hx
    by_contra h0
    have : x ∈ m := h0
    rw [hm, Ideal.mem_span_singleton] at this
    exact hi.not_isUnit (isUnit_of_dvd_unit (map_dvd i this) hx)
  · intro a
    change q (algebraMap K T a ⊗ₜ[K] (1 : F)) = q ((1 : T) ⊗ₜ[K] algebraMap K F a)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory.DVRBaseChange
