import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFibreCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open GroundTheory.Arith.Abelian.Jacobian

theorem CodimOnePrimeAvoid.proof : CodimOnePrimeAvoid.Statement := by
  intro k B _ _ _ _ _ h hh hdim
  let Bh := Localization.Away h
  have hle : Submonoid.powers h ≤ nonZeroDivisors B :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hh
  have : IsDomain Bh := IsLocalization.isDomain_localization hle
  have : Algebra.FinitePresentation B Bh := IsLocalization.Away.finitePresentation (S := Bh) h
  have : Algebra.FiniteType B Bh := inferInstance
  have : Algebra.FiniteType k Bh := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have : IsNoetherianRing Bh := Algebra.FiniteType.isNoetherianRing k Bh
  let K := FractionRing B
  have hu : ∀ y : Submonoid.powers h, IsUnit (algebraMap B K y) := fun y =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective B K)).2
      (nonZeroDivisors.ne_zero (hle y.2)))
  let _ : Algebra Bh K := (IsLocalization.lift (M := Submonoid.powers h) (S := Bh) hu).toAlgebra
  have : IsScalarTower B Bh K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := Submonoid.powers h) (S := Bh) hu x).symm
  have : IsScalarTower k Bh K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply k B K, IsScalarTower.algebraMap_apply k B Bh,
      ← IsScalarTower.algebraMap_apply B Bh K]
  have : IsFractionRing Bh K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers h) Bh K
  have hdimh : ringKrullDim Bh = ringKrullDim B := by
    rw [ringKrullDim_eq_trdeg_fractionRing k K, ringKrullDim_eq_trdeg_fractionRing k K]
  have hnf : ¬ IsField Bh := fun hf => by
    have h0 := ringKrullDim_eq_zero_of_isField hf
    rw [hdimh] at h0
    rw [h0] at hdim
    exact absurd hdim (by decide)
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 hnf
  obtain ⟨x, hxp, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem p).2 hxp)
  have hqp : q.IsPrime := hq.isPrime
  have hxq : x ∈ q := (Ideal.span_singleton_le_iff_mem q).1 hq.1.2
  have hq1 : q.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    rintro rfl
    exact hx0 hxq
  refine ⟨q.comap (algebraMap B Bh), hqp.comap _, fun hhN => hqp.ne_top ?_, ?_⟩
  · exact Ideal.eq_top_of_isUnit_mem _ hhN (IsLocalization.Away.algebraMap_isUnit h)
  · have hN := IsLocalization.height_under (Submonoid.powers h) q
    rw [hq1] at hN
    have := height_add_ringKrullDim_quotient k (q.comap (algebraMap B Bh))
    rw [Ideal.under] at hN
    rw [hN] at this
    rw [← this, add_comm]
    rfl

end GroundTheory.Heights₂.Heights.Vertical
