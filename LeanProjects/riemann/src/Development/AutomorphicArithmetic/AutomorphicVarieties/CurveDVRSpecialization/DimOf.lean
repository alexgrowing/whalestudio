import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Component
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

theorem UpperTheory.V.Pr.dimOf :
    UpperTheory.V.Pr.DimOf := by
  intro O Λ B _ _ _ _ _ _ _ φ J m ⟨e⟩ hfin htf Z hZ
  haveI : NoZeroDivisors O := IsDomain.to_noZeroDivisors O
  haveI : IsPrincipalIdealRing O := IsDiscreteValuationRing.toIsPrincipalIdealRing
  haveI : IsNoetherianRing O := PrincipalIdealRing.isNoetherianRing
  haveI : IsLocalRing O := IsDiscreteValuationRing.toIsLocalRing
  haveI : NoZeroDivisors (MvPowerSeries (Fin m) O) := inferInstance
  haveI : Nontrivial (MvPowerSeries (Fin m) O) := inferInstance
  haveI : IsDomain (MvPowerSeries (Fin m) O) := NoZeroDivisors.to_isDomain _
  haveI : IsDomain Λ := e.toMulEquiv.isDomain
  letI : Algebra Λ (B ⧸ J) := ((Ideal.Quotient.mk J).comp φ).toAlgebra
  haveI : Module.Finite Λ (B ⧸ J) := hfin
  haveI : Algebra.IsIntegral Λ (B ⧸ J) := Algebra.IsIntegral.of_finite Λ (B ⧸ J)
  have hJZ : J ≤ Z := hZ.1.2
  have hZ' := hZ
  rw [Ideal.minimalPrimes_eq_comap] at hZ'
  obtain ⟨P, hP, rfl⟩ := hZ'
  have hnz : ∀ a : Λ, a ≠ 0 → algebraMap Λ (B ⧸ J) a ∈ nonZeroDivisors (B ⧸ J) := by
    intro a ha
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine htf a ha b ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hx
  have h := (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.component Λ (B ⧸ J) hnz P hP).2.2
  have hq : ringKrullDim (B ⧸ P.comap (Ideal.Quotient.mk J)) = ringKrullDim ((B ⧸ J) ⧸ P) := by
    have hs : Function.Surjective ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk J)) :=
      Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    have hk : P.comap (Ideal.Quotient.mk J)
        = RingHom.ker ((Ideal.Quotient.mk P).comp (Ideal.Quotient.mk J)) := by
      ext x
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
    rw [hk]
    exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hs)
  show ringKrullDim _ = _
  rw [hq, h, ringKrullDim_eq_of_ringEquiv e.toRingEquiv,
    GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
