import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedCubicalRootPolarisationEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackPasteFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsEtaleCompletionCompOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomAndIsAdicCompleteOfFiniteDvr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.HenselLift

theorem exists_dvr_of_finite_etale : ∀ (A R V : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (ρ : A →+* R) (ψ : A →+* V), IsLocalHom ρ → ρ.Finite → ρ.Etale → IsCN V → IsDiscreteValuationRing V → IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : R →+* V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp ρ = f.comp ψ := by
  intro A R V _ _ _ _ _ _ _ ρ ψ hρl hρf hρe hV hdvr hψ
  letI := ρ.toAlgebra
  letI := ψ.toAlgebra
  obtain ⟨hnoeth, hic, hcpl, hchar⟩ := hV
  haveI : Algebra.Etale A R := hρe
  haveI : Module.Finite A R := hρf
  haveI : IsLocalHom (algebraMap A R) := hρl
  haveI : IsLocalHom (algebraMap A V) := hψ
  haveI : Algebra.Etale V (V ⊗[A] R) := Algebra.Etale.baseChange A R V
  haveI : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI : Nontrivial (V ⊗[A] R) := Module.FaithfullyFlat.rTensor_nontrivial A R V
  obtain ⟨q, hq⟩ := Ideal.exists_maximal (V ⊗[A] R)
  haveI : HenselianLocalRing V := GlobalTheory.henselianLocalRing_of_isAdicComplete V
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian V q
  haveI := GlobalTheory.isLocalRing_quotient_one_sub he q H
  haveI : IsLocalization.Away e (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  haveI : Algebra.Etale (V ⊗[A] R) (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    Algebra.Etale.of_isLocalizationAway e
  haveI : Algebra.Etale V (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    Algebra.Etale.comp V (V ⊗[A] R) _
  haveI : Module.Finite V (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    Module.Finite.trans (V ⊗[A] R) _
  have hfl : IsLocalHom (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})) := by
    refine ((local_hom_TFAE _).out 0 4).2 ?_
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := V)
      (maximalIdeal (V ⊗[A] R ⧸ Ideal.span {1 - e}))
    exact IsLocalRing.eq_maximalIdeal this
  haveI := hfl
  obtain ⟨hdom, hdvr', -, hff, -⟩ :=
    GlobalTheory.isDiscreteValuationRing_of_etale_of_isLocalHom V (V ⊗[A] R ⧸ Ideal.span {1 - e})
  have hinj : Function.Injective (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})) :=
    FaithfulSMul.algebraMap_injective _ _
  haveI : IsNoetherianRing V := hnoeth
  haveI : IsAdicComplete (maximalIdeal V) V := hcpl
  haveI : CharZero V := hchar
  obtain ⟨-, hcpl'⟩ := GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr V
    (V ⊗[A] R ⧸ Ideal.span {1 - e}) inferInstance hinj
  have hcomm : ((Ideal.Quotient.mk (Ideal.span {1 - e})).comp
      (Algebra.TensorProduct.includeRight.toRingHom)).comp ρ =
      (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})).comp ψ := by
    ext a
    show Ideal.Quotient.mk _ ((1 : V) ⊗ₜ[A] ρ a) = Ideal.Quotient.mk _ (ψ a ⊗ₜ[A] (1 : R))
    rw [show ρ a = a • (1 : R) from Algebra.algebraMap_eq_smul_one a,
      show ψ a = a • (1 : V) from Algebra.algebraMap_eq_smul_one a, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  refine ⟨V ⊗[A] R ⧸ Ideal.span {1 - e}, inferInstance, hdom, inferInstance,
    algebraMap V _, (Ideal.Quotient.mk _).comp (Algebra.TensorProduct.includeRight.toRingHom),
    ⟨?_, inferInstance, hcpl', charZero_of_injective_algebraMap hinj⟩, hdvr', hinj,
    RingHom.finite_algebraMap.2 inferInstance, inferInstance, ?_, ?_⟩
  · exact isNoetherian_of_tower V inferInstance
  · refine ((local_hom_TFAE _).out 0 4).2 ?_
    have hA : Ideal.comap (algebraMap A R) (Ideal.comap ((Ideal.Quotient.mk (Ideal.span {1 - e})).comp
        (Algebra.TensorProduct.includeRight.toRingHom)) (maximalIdeal _)) = maximalIdeal A := by
      have h1 : Ideal.comap (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})) (maximalIdeal _) =
          maximalIdeal V := ((local_hom_TFAE _).out 0 4).1 hfl
      have h2 : Ideal.comap ψ (maximalIdeal V) = maximalIdeal A := ((local_hom_TFAE _).out 0 4).1 hψ
      change Ideal.comap ρ _ = _
      rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap, h1, h2]
    have hA' : (Ideal.comap (algebraMap A R) (Ideal.comap ((Ideal.Quotient.mk (Ideal.span {1 - e})).comp
        (Algebra.TensorProduct.includeRight.toRingHom)) (maximalIdeal _))).IsMaximal := by
      rw [hA]; exact maximalIdeal.isMaximal A
    have hm := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) _ hA'
    exact IsLocalRing.eq_maximalIdeal hm
  · exact hcomm

end GlobalTheory.HenselLift
