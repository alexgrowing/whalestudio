import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.LocExt

theorem exists_finite_normal_cover_of_finiteDimensional : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (τ : K' →+* FractionRing R'), Function.Injective ρ ∧ ρ.Finite ∧ ((τ.comp (algebraMap (FractionRing R) K')).comp (algebraMap R (FractionRing R))) = (algebraMap R' (FractionRing R')).comp ρ := by
  intro R _ _ _ _ hcomp K' _ _ _
  have hnorm : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  have hCN : IsCN R := ⟨inferInstance, hnorm, hcomp, inferInstance⟩
  let K := FractionRing R
  letI : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  haveI : Algebra.IsSeparable K K' := inferInstance
  let C := integralClosure R K'
  haveI hCf : Module.Finite R C := IsIntegralClosure.finite R K K' C
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension K K'
  have hRK' : Function.Injective (algebraMap R K') := by
    rw [IsScalarTower.algebraMap_eq R K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective R K)
  have hRC : Function.Injective (algebraMap R C) := fun x y h => hRK' (congrArg Subtype.val h)
  obtain ⟨R', _, _, _, ρ, σ, hCN', hρ, hρf, -, hσρ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (algebraMap R C) hCN hRC
      (RingHom.finite_algebraMap.2 hCf)
  obtain ⟨hnoeth', hnorm', -, -⟩ := hCN'
  letI : Algebra C R' := σ.toAlgebra
  letI : Algebra R R' := ρ.toAlgebra
  haveI : IsScalarTower R C R' := IsScalarTower.of_algebraMap_eq (fun r => (RingHom.congr_fun hσρ r).symm)
  haveI : Algebra.IsIntegral R C := Algebra.IsIntegral.of_finite R C
  have hσ : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hker : RingHom.ker σ = ⊥ := by
      apply Ideal.eq_bot_of_comap_eq_bot (R := R)
      ext r
      simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      constructor
      · intro h
        apply hρ
        rw [map_zero, ← h]
        exact (RingHom.congr_fun hσρ r).symm
      · rintro rfl; simp
    have : c ∈ RingHom.ker σ := hc
    rw [hker] at this
    exact this
  have hσ' : Function.Injective ((algebraMap R' (FractionRing R')).comp σ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hσ
  let τ : K' →+* FractionRing R' := IsFractionRing.lift (A := C) hσ'
  refine ⟨R', inferInstance, inferInstance, hnoeth', hnorm', inferInstance, ρ, τ, hρ, hρf, ?_⟩
  ext r
  simp only [RingHom.comp_apply]
  have h1 : algebraMap K K' (algebraMap R K r) = algebraMap C K' (algebraMap R C r) := rfl
  rw [h1]
  simp only [τ, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  rw [← RingHom.comp_apply σ, hσρ]

end GlobalTheory.LocExt
