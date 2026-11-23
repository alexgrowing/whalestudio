import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero

open GlobalTheory.PrimSec in

theorem exists_open_pull_eq_zero {O K : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O]
    [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] {X XK : Scheme.{0}} {f : X ⟶ Sp O} {j : XK ⟶ X}
    {fK : XK ⟶ Sp K} (H : IsPullback j fK f (spMap (algebraMap O K))) [Smooth f] [GeometricallyIntegral f]
    {x : X} (hfx : f x = IsLocalRing.closedPoint O) (l : Pic XK) :
    ∃ V : X.Opens, (∃ y ∈ V, f y = IsLocalRing.closedPoint O) ∧ pull (j ⁻¹ᵁ V).ι l = 0 := by
  haveI : IsIntegral XK := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  obtain ⟨V, hV, hxV, -, n, φ, hφ, hφ'⟩ := exists_etale_chart f (U := ⊤) (x := x) trivial
  have hp := isPrime_map f hV hxV hfx
  have hinj := app_injective H V
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hne : Nonempty (j ⁻¹ᵁ V) :=
    nonempty_of_ne_zero (a := 1) fun h => one_ne_zero (hinj ((map_one _).trans (h.trans (map_zero _).symm)))
  haveI : IsDomain Γ(X, V) := hinj.isDomain _
  obtain ⟨⟨p, hpV⟩⟩ := id hne
  obtain ⟨W, hpW, hW⟩ := exists_pull_eq_zero l p
  have hjV : IsAffineOpen (j ⁻¹ᵁ V) := by
    haveI : IsAffineHom j := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
    exact hV.preimage j
  obtain ⟨σ, hσW, hpσ⟩ := hjV.exists_basicOpen_le (V := W) ⟨p, hpW⟩ hpV
  obtain ⟨π, b, hπ, hb⟩ := exists_numerator H hV σ
  have hπ' : algebraMap O K π ≠ 0 := fun h => hπ (IsFractionRing.injective O K (h.trans (map_zero _).symm))
  have hc : ∀ c : K, c ≠ 0 → ∀ z ∈ j ⁻¹ᵁ V, z ∈ XK.basicOpen (AbLaw.cst fK (j ⁻¹ᵁ V) c) := fun c hc z hz =>
    (mem_basicOpen_cst fK _ c hz).2 fun h => hc (by
      haveI := (fK z).isPrime
      have e : (fK z).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
      rw [e] at h
      exact h)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    have h0 : p ∈ XK.basicOpen (0 : Γ(XK, j ⁻¹ᵁ V)) := by
      rw [hb, Scheme.basicOpen_mul]
      exact ⟨hc _ hπ' p hpV, hpσ⟩
    rw [Scheme.basicOpen_zero] at h0
    exact h0
  letI := (AbLaw.cst f V).toAlgebra
  letI := φ.toAlgebra
  haveI : IsScalarTower O (MvPolynomial (Fin n) O) Γ(X, V) := .of_algebraMap_eq' hφ.symm
  haveI : Algebra.Etale (MvPolynomial (Fin n) O) Γ(X, V) := hφ'
  obtain ⟨ρ, b', e, hb'⟩ := GlobalTheory.etale_mvPolynomial_exists_content O K n Γ(X, V) hp b hb0
  obtain ⟨y, hy⟩ := hV.isoSpec.hom.surjective
    (⟨(IsLocalRing.maximalIdeal O).map (AbLaw.cst f V), hp⟩ : PrimeSpectrum Γ(X, V))
  have hy' : (hV.primeIdealOf y).asIdeal = (IsLocalRing.maximalIdeal O).map (AbLaw.cst f V) :=
    congrArg PrimeSpectrum.asIdeal hy
  refine ⟨X.basicOpen b', ⟨y.1, (mem_basicOpen_iff hV y b').2 (hy' ▸ hb'), ?_⟩,
    pull_eq_zero_of_mem W _ (fun z => ?_) hW⟩
  · refine PrimeSpectrum.ext (((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (f y.1).isPrime.ne_top
      fun a ha => ?_).symm)
    by_contra h
    exact (mem_basicOpen_iff hV y _).1 ((mem_basicOpen_cst f V a y.2).2 h) (hy' ▸ Ideal.mem_map_of_mem _ ha)
  · have hz : j z.1 ∈ X.basicOpen b' := z.2
    have hzV : z.1 ∈ j ⁻¹ᵁ V := X.basicOpen_le b' hz
    have hz' : z.1 ∈ XK.basicOpen ((j.app V).hom b') := by
      rw [← Scheme.preimage_basicOpen]
      exact hz
    have hρ : algebraMap O K ρ ≠ 0 := fun h => hb0 (by
      rw [e, IsFractionRing.injective O K (h.trans (map_zero _).symm), map_zero, zero_mul])
    have e' : (j.app V).hom b = AbLaw.cst fK (j ⁻¹ᵁ V) (algebraMap O K ρ) * (j.app V).hom b' := by
      rw [e, map_mul]
      change (j.app V).hom (AbLaw.cst f V ρ) * _ = _
      rw [app_cst H.w]
    have h1 : z.1 ∈ XK.basicOpen ((j.app V).hom b) := by
      rw [e', Scheme.basicOpen_mul]
      exact ⟨hc _ hρ _ hzV, hz'⟩
    rw [hb, Scheme.basicOpen_mul] at h1
    exact hσW h1.2

theorem near_zero : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ l : Pic (pullback A.hom (spMap (algebraMap R C))),
      ∃ V : A.left.Opens, (∃ y ∈ V, A.hom y = IsLocalRing.closedPoint R) ∧
        pull (pullback.fst A.hom (spMap (algebraMap R C)) ⁻¹ᵁ V).ι l = 0 := by
  intro C _ _ R _ _ _ _ _ _ A _ hA l
  have := hA.smooth
  have := hA.geomConnected
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ A
  obtain ⟨x, hx⟩ := A.hom.surjective (IsLocalRing.closedPoint R)
  exact exists_open_pull_eq_zero (IsPullback.of_hasPullback A.hom (spMap (algebraMap R C))) hx l

end GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.NearZero
