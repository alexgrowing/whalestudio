import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem faithfullyFlat_adicCompletion_span (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (t : R) (ht : t ∈ maximalIdeal R) :
    Module.FaithfullyFlat R (AdicCompletion (Ideal.span {t}) R) := by
  haveI : Module.Flat R (AdicCompletion (Ideal.span {t}) R) := AdicCompletion.flat_of_isNoetherian _
  refine ⟨fun m hm => ?_⟩
  rw [IsLocalRing.eq_maximalIdeal hm]
  have hle : Ideal.span {t} ≤ maximalIdeal R := (Ideal.span_singleton_le_iff_mem _).2 ht
  have hmax := AdicCompletion.isMaximal_map_of_le (Ideal.span {t}) (maximalIdeal R) hle
    (Submodule.fg_span_singleton t)
  intro h
  apply hmax.ne_top
  have e := Ideal.smul_top_eq_map (S := AdicCompletion (Ideal.span {t}) R) (maximalIdeal R)
  rw [h] at e
  apply Submodule.restrictScalars_injective R
  rw [← e]; rfl

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem exists_integral_point (A R C : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing R] [CommRing C] [Algebra R C] (ρ : R →+* A) (hint : Algebra.IsIntegral R C)
    (s : C →+* FractionRing A) (hs : s.comp (algebraMap R C) = (algebraMap A (FractionRing A)).comp ρ) :
    ∃ g : C →+* A, (algebraMap A (FractionRing A)).comp g = s ∧ g.comp (algebraMap R C) = ρ := by
  set K := FractionRing A
  have hmem : ∀ c : C, s c ∈ (algebraMap A K).range := by
    intro c
    obtain ⟨p, hp, hpc⟩ := hint.isIntegral c
    have hi : IsIntegral A (s c) := by
      refine ⟨p.map ρ, hp.map ρ, ?_⟩
      rw [Polynomial.eval₂_map, ← hs, ← Polynomial.hom_eval₂, hpc, map_zero]
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hi
    exact ⟨a, ha⟩
  let e := RingEquiv.ofBijective (algebraMap A K).rangeRestrict
    ⟨fun x y h => IsFractionRing.injective A K (congrArg Subtype.val h),
     (algebraMap A K).rangeRestrict_surjective⟩
  let g : C →+* A := e.symm.toRingHom.comp (s.codRestrict _ hmem)
  have hg : (algebraMap A K).comp g = s := by
    ext c
    have : e (g c) = s.codRestrict _ hmem c := by simp [g]
    exact congrArg Subtype.val this
  refine ⟨g, hg, ?_⟩
  ext r
  apply IsFractionRing.injective A K
  have := congrArg (fun f => f r) hs
  simp only [RingHom.comp_apply] at this
  change (algebraMap A K) (g (algebraMap R C r)) = _
  rw [← this, ← hg, RingHom.comp_apply]
  rfl

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem mem_pow_of_mul_mem_pow (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R)
    (a : A) (ha : a ≠ 0) : ∀ (n : ℕ) (r : R), algebraMap A R a * r ∈ Ideal.span {t ^ n} →
      r ∈ Ideal.span {t ^ n} := by
  have hρa : ρ (algebraMap A R a) = a := by
    simpa using congrArg (fun f => f a) hρ
  intro n
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r hr
    have hr1 : algebraMap A R a * r ∈ RingHom.ker ρ := by
      rw [hker, Ideal.mem_span_singleton]
      exact (dvd_pow_self t (Nat.succ_ne_zero n)).trans (Ideal.mem_span_singleton.1 hr)
    rw [RingHom.mem_ker, map_mul, hρa] at hr1
    have hr0 : r ∈ Ideal.span {t} := by
      rw [← hker, RingHom.mem_ker]
      exact (mul_eq_zero.1 hr1).resolve_left ha
    obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton.1 hr0
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hr
    have h2 : algebraMap A R a * r' = t ^ n * q := by
      have : t * (algebraMap A R a * r') = t * (t ^ n * q) := by
        rw [pow_succ] at hq
        linear_combination hq
      have h3 : t * (algebraMap A R a * r' - t ^ n * q) = 0 := by rw [mul_sub, this, sub_self]
      exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff ht).1 h3)
    have := ih r' (Ideal.mem_span_singleton.2 ⟨q, h2⟩)
    obtain ⟨q', rfl⟩ := Ideal.mem_span_singleton.1 this
    exact Ideal.mem_span_singleton.2 ⟨q', by ring⟩

theorem torsionFree_quot : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.TorsionFreeOver A R (R ⧸ Ideal.span {t} ^ n) := by
  intro A R _ _ _ _ ρ hρ t hker ht n a ha m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow] at hm
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
  exact mem_pow_of_mul_mem_pow A R ρ hρ t hker ht a ha n r hm

end GlobalTheory.GoodEtaleSection
