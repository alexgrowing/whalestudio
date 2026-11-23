import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RingKrullDimQuotientOfMemAssociatedPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.adicComplete
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem psBase_equiv {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (h : IsBase A) : IsBase B := by
  have hd : IsDomain A := h.dom
  have hn : IsIntegrallyClosed A := h.normal
  have hc : IsAdicComplete (maximalIdeal A) A := h.complete
  refine ⟨MulEquiv.isDomain A e.symm.toMulEquiv, IsIntegrallyClosed.of_equiv e, h.cm.of_ringEquiv e, ?_⟩
  have hm : Ideal.map e (maximalIdeal A) = maximalIdeal B := by
    ext x
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      intro hu
      apply hy
      simpa using hu.map e.symm
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      intro hu
      apply hx
      simpa using hu.map e
  rw [← hm]
  exact (IsAdicComplete.congr_ringEquiv _ e).2 hc

private theorem psBase_cm (R : Type) [CommRing R] [IsLocalRing R] [IsDomain R]
    (h : ReciprocityTheory.CA.IsCM R) : ReciprocityTheory.CA.IsCM (PowerSeries R) := by
  haveI := h.1
  have hker : Ideal.span {(PowerSeries.X : PowerSeries R)} =
      RingHom.ker (PowerSeries.constantCoeff : PowerSeries R →+* R) := by
    ext f
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, PowerSeries.X_dvd_iff]
  have hsurj : Function.Surjective (PowerSeries.constantCoeff : PowerSeries R →+* R) :=
    fun a => ⟨PowerSeries.C a, by simp⟩
  let e : (PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R)}) ≃+* R :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  haveI : IsLocalRing (PowerSeries R ⧸ Ideal.span {(PowerSeries.X : PowerSeries R)}) :=
    e.symm.isLocalRing
  refine ReciprocityTheory.CA.isCM_of_quotient_span_singleton (x := PowerSeries.X) ?_
    (mem_nonZeroDivisors_of_ne_zero PowerSeries.X_ne_zero) (h.of_ringEquiv e.symm)
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simp

private theorem psBase_one (R : Type) [CommRing R] [IsLocalRing R] (h : IsBase R) :
    IsBase (PowerSeries R) := by
  haveI := h.dom
  haveI := h.normal
  haveI := h.cm.1
  haveI := h.complete
  exact ⟨inferInstance, GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries R,
    psBase_cm R h.cm, UpperTheory.V.abelian₂.adicComplete R⟩

theorem UpperTheory.V.AlgebraTools.Conn.psBase :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], IsBase O → ∀ n : ℕ, IsBase (MvPowerSeries (Fin n) O) := by
  intro O _ _ hO n
  induction n with
  | zero =>
    have hbij : Function.Bijective
        (MvPowerSeries.constantCoeff (σ := Fin 0) (R := O)) := by
      refine ⟨fun f g hfg => ?_, fun a => ⟨MvPowerSeries.C a, by simp⟩⟩
      ext d
      have hd : d = 0 := Subsingleton.elim _ _
      subst hd
      simpa using hfg
    exact psBase_equiv (RingEquiv.ofBijective _ hbij).symm hO
  | succ n ih =>
    exact psBase_equiv (MvPowerSeries.finSuccEquiv O n).toRingEquiv.symm (psBase_one _ ih)
