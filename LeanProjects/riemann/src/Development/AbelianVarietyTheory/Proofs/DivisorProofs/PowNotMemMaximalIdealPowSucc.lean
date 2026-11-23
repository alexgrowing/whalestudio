import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ReducedFibre

theorem pow_notMem_maximalIdeal_pow_succ {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) (hreg : π ∈ nonZeroDivisors R) (k : ℕ) :
    π ^ k ∉ maximalIdeal R ^ (k + 1) := by
  intro h
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have h1 : π ^ k * (1 - π * c) = 0 := by
    linear_combination hc
  have h2 : 1 - π * c = 0 := (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hreg k)).mp h1
  have hmem : π ∈ maximalIdeal R := by rw [hπ]; exact Ideal.mem_span_singleton_self π
  exact (mem_maximalIdeal π).mp hmem (isUnit_iff_exists_inv.mpr ⟨c, by linear_combination -h2⟩)

theorem adicCompletion_dvr {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) (hreg : π ∈ nonZeroDivisors R)
    (fg : (maximalIdeal R).FG) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    ∃ _ : IsDomain (AdicCompletion (maximalIdeal R) R),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal R) R) ∧
      Irreducible (algebraMap R (AdicCompletion (maximalIdeal R) R) π) := by
  haveI := AdicCompletion.isLocalRing_of_fg fg
  haveI := AdicCompletion.isAdicComplete_of_fg fg
  refine GlobalTheory.isDiscreteValuationRing_of_maximalIdeal_eq_span ?_ ?_
  · rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg, hπ, Ideal.map_span, Set.image_singleton]
  · rintro ⟨k, hk⟩
    rw [← map_pow] at hk
    have h := congrArg (AdicCompletion.eval (maximalIdeal R) R (k + 1)) hk
    rw [show algebraMap R (AdicCompletion (maximalIdeal R) R) (π ^ k) =
      AdicCompletion.of (maximalIdeal R) R (π ^ k) from rfl, AdicCompletion.eval_of, map_zero,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top] at h
    exact pow_notMem_maximalIdeal_pow_succ hπ hreg k h

end GlobalTheory.ReducedFibre

namespace GlobalTheory.ReducedFibre

theorem exists_notMem_mul_eq_zero {A : Type*} [CommRing A] [IsReduced A]
    {Q : Ideal A} (hQ : Q ∈ minimalPrimes A) {x : A} (hx : x ∈ Q) :
    ∃ s : A, s ∉ Q ∧ s * x = 0 := by
  haveI : Q.IsPrime := hQ.1.1
  have hsub := IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes Q hQ
    (Localization.AtPrime Q)
  have hmem : algebraMap A (Localization.AtPrime Q) x ∈ maximalIdeal _ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ hx
  have hnil : IsNilpotent (algebraMap A (Localization.AtPrime Q) x) := by
    rw [nilpotent_iff_mem_prime]
    intro Q' hQ'
    have h1 : (⟨Q', hQ'⟩ : PrimeSpectrum (Localization.AtPrime Q)) =
        ⟨maximalIdeal _, inferInstance⟩ := Subsingleton.elim _ _
    rw [show Q' = maximalIdeal _ from congrArg PrimeSpectrum.asIdeal h1]
    exact hmem
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ x).mp hnil.eq_zero
  exact ⟨s, s.2, hs⟩

theorem exists_cdvr_of_flat_of_isReduced :
    ∀ (V C : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing C] [Algebra V C]
      [Module.Flat V C], Nontrivial (C ⧸ (maximalIdeal V).map (algebraMap V C)) →
      IsReduced (C ⧸ (maximalIdeal V).map (algebraMap V C)) →
      ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
        (h : C →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
        ∀ ϖ : V, Irreducible ϖ → Irreducible (h (algebraMap V C ϖ)) := by
  intro V C _ _ _ _ _ _ hnt hred
  set J : Ideal C := (maximalIdeal V).map (algebraMap V C) with hJ
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (C ⧸ J)
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal (C ⧸ J)) ≤ M)
  haveI : Q.IsPrime := hQ.1.1
  set P : Ideal C := Q.comap (Ideal.Quotient.mk J) with hP
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  let R := Localization.AtPrime P
  have hJP : J ≤ P := fun x hx => by
    rw [hP, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Q.zero_mem
  have hmax : maximalIdeal R = (maximalIdeal V).map (algebraMap V R) := by
    rw [IsScalarTower.algebraMap_eq V C R, ← Ideal.map_map, ← hJ,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    refine le_antisymm ?_ (Ideal.map_mono hJP)
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨s', hs', hs'a⟩ := exists_notMem_mul_eq_zero hQ (show Ideal.Quotient.mk J a ∈ Q from ha)
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
    have hsP : s ∈ P.primeCompl := hs'
    have hsa : s * a ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_mul]; exact hs'a)
    rw [Ideal.mem_comap]
    have hu : IsUnit (algebraMap C R s) := IsLocalization.map_units R (⟨s, hsP⟩ : P.primeCompl)
    have := Ideal.mem_map_of_mem (algebraMap C R) hsa
    rw [map_mul] at this
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp this
  have hspan : ∀ ϖ : V, Irreducible ϖ → maximalIdeal R = Ideal.span {algebraMap V R ϖ} := by
    intro ϖ hϖ
    rw [hmax, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hreg : ∀ v : V, v ≠ 0 → algebraMap V R v ∈ nonZeroDivisors R := by
    intro v hv
    haveI : Module.Flat V R := Module.Flat.trans V C R
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) (mem_nonZeroDivisors_of_ne_zero hv)
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => h ?_, fun x hx => h ?_⟩
    · show v • x = v • (0 : R)
      rw [smul_zero, Algebra.smul_def, hx]
    · show v • x = v • (0 : R)
      rw [smul_zero, Algebra.smul_def, mul_comm, hx]
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible V
  have fg : (maximalIdeal R).FG := ⟨{algebraMap V R ϖ₀}, by rw [hspan ϖ₀ hϖ₀]; simp⟩
  haveI := AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hd, hdvr, -⟩ := adicCompletion_dvr (hspan ϖ₀ hϖ₀) (hreg ϖ₀ hϖ₀.ne_zero) fg
  refine ⟨AdicCompletion (maximalIdeal R) R, inferInstance, hd, hdvr,
    (algebraMap R (AdicCompletion (maximalIdeal R) R)).comp (algebraMap C R),
    AdicCompletion.isAdicComplete_of_fg fg, fun ϖ hϖ => ?_⟩
  obtain ⟨-, -, hirr⟩ := adicCompletion_dvr (hspan ϖ hϖ) (hreg ϖ hϖ.ne_zero) fg
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  exact hirr

end GlobalTheory.ReducedFibre
