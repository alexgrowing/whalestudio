import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoCaten
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.htPres :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (N N' : ℕ) (R : Type) [CommRing R]
        (p : MvPowerSeries (Fin N) O →+* R) (f : Fin N' → MvPowerSeries (Fin N) O), Function.Surjective p → RingHom.ker p = Ideal.span (Set.range f) →
        ∀ Q : Ideal R, Q.IsPrime → ((Q.comap p).height : WithBot ℕ∞) + ringKrullDim (R ⧸ Q) = (N + 1 : ℕ) ∧ (Q.comap p).height ≤ Q.height + N' := by
  intro O _ _ _ _ N N' R _ p f hp hker Q hQ
  haveI : IsPrincipalIdealRing O := IsDiscreteValuationRing.toIsPrincipalIdealRing
  haveI : IsNoetherianRing O := PrincipalIdealRing.isNoetherianRing
  haveI : IsCO O O := IsCO.self O
  haveI : IsCO O (MvPowerSeries (Fin N) O) := co_mvps O O (Fin N)
  haveI : IsNoetherianRing (MvPowerSeries (Fin N) O) := MvPowerSeries.isNoetherianRing O
  haveI : NoZeroDivisors (MvPowerSeries (Fin N) O) := inferInstance
  haveI : IsDomain (MvPowerSeries (Fin N) O) := NoZeroDivisors.to_isDomain _
  haveI hP : (Q.comap p).IsPrime := Ideal.comap_isPrime p Q
  have hdim : ringKrullDim (MvPowerSeries (Fin N) O) = ((N + 1 : ℕ) : WithBot ℕ∞) := (CA.cl_cm.1 O N).2
  have hsurj : Function.Surjective ((Ideal.Quotient.mk Q).comp p) :=
    (Ideal.Quotient.mk_surjective).comp hp
  have hk : RingHom.ker ((Ideal.Quotient.mk Q).comp p) = Q.comap p := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  have eQ : (MvPowerSeries (Fin N) O ⧸ Q.comap p) ≃+* (R ⧸ Q) :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  constructor
  · rw [← ringKrullDim_eq_of_ringEquiv eQ, ← hdim]
    exact co_caten O (MvPowerSeries (Fin N) O) (Q.comap p)
  · set K := RingHom.ker p
    let e : (MvPowerSeries (Fin N) O ⧸ K) ≃+* R := RingHom.quotientKerEquivOfSurjective hp
    have hmap : (Q.comap p).map (Ideal.Quotient.mk K) = Q.comap (e : (MvPowerSeries (Fin N) O ⧸ K) →+* R) := by
      have : Q.comap p = (Q.comap (e : (MvPowerSeries (Fin N) O ⧸ K) →+* R)).comap (Ideal.Quotient.mk K) := by
        rw [Ideal.comap_comap]
        congr 1
      rw [this, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have hsub : Set.range f ⊆ (Q.comap p : Set (MvPowerSeries (Fin N) O)) := by
      rintro _ ⟨i, rfl⟩
      have : f i ∈ K := by
        rw [hker]
        exact Ideal.subset_span ⟨i, rfl⟩
      show p (f i) ∈ Q
      rw [RingHom.mem_ker.mp this]
      exact Q.zero_mem
    have h1 := Ideal.height_le_height_add_encard_of_subset (Set.range f) hsub
    rw [← hker, hmap] at h1
    have he : (Q.comap (e : (MvPowerSeries (Fin N) O ⧸ K) →+* R)).height = Q.height :=
      RingEquiv.height_comap e Q
    rw [he] at h1
    refine h1.trans ?_
    gcongr
    calc (Set.range f).encard ≤ (Set.univ : Set (Fin N')).encard := by
          rw [← Set.image_univ]
          exact Set.encard_image_le _ _
      _ = N' := by
          rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
