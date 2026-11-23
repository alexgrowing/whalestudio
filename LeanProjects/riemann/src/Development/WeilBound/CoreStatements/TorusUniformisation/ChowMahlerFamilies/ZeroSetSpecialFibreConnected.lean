import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ZariskiConnected
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.SpecialFibreConnected

theorem mem_range_of_isIntegral {O Ω : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field Ω]
    [Algebra O Ω] (hinj : Function.Injective (algebraMap O Ω)) (hc : ConstClosed O Ω) (a : Ω)
    (ha : IsIntegral O a) : ∃ o : O, algebraMap O Ω o = a := by
  obtain ⟨x, y, hy, e⟩ := hc a ha.isAlgebraic
  let ι : FractionRing O →ₐ[O] Ω :=
    { IsFractionRing.lift (K := FractionRing O) hinj with
      commutes' := fun o => IsFractionRing.lift_algebraMap hinj o }
  have hy' : algebraMap O Ω y ≠ 0 := fun h => hy (hinj (by rw [h, map_zero]))
  have e' : ι (algebraMap O (FractionRing O) x / algebraMap O (FractionRing O) y) = a := by
    rw [map_div₀, ι.commutes, ι.commutes, ← e, mul_div_cancel_right₀ _ hy']
  have hi : IsIntegral O (algebraMap O (FractionRing O) x / algebraMap O (FractionRing O) y) := by
    rw [← isIntegral_algHom_iff ι ι.toRingHom.injective, e']
    exact ha
  obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨o, by rw [← e', ← ho, ι.commutes]⟩

theorem appTop_injective {Z : Scheme.{0}} [IsReduced Z] {Ω : Type} [Field Ω]
    (η : Spec (CommRingCat.of Ω) ⟶ Z) (h : ∀ q : Z, η (IsLocalRing.closedPoint Ω) ⤳ q) :
    Function.Injective η.appTop.hom := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro q hq
  have h1 : η (IsLocalRing.closedPoint Ω) ∈ Z.basicOpen t :=
    (h q).mem_open (Z.basicOpen t).isOpen hq
  have h2 : IsLocalRing.closedPoint Ω ∈ η ⁻¹ᵁ Z.basicOpen t := h1
  rw [Scheme.preimage_basicOpen_top] at h2
  have h3 : η.appTop t = 0 := ht
  rw [h3, Scheme.basicOpen_zero] at h2
  exact h2.elim

theorem bijective_const {Z : Scheme.{0}} [IsReduced Z] {Ω : Type} [Field Ω]
    (η : Spec (CommRingCat.of Ω) ⟶ Z) (h : ∀ q : Z, η (IsLocalRing.closedPoint Ω) ⤳ q)
    {O : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra O Ω]
    (f : Z ⟶ Spec (CommRingCat.of O)) [IsProper f] (hinj : Function.Injective (algebraMap O Ω))
    (hf : η ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) (hc : ConstClosed O Ω) :
    Function.Bijective (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom) := by
  let ψ : O →+* Γ(Z, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  let φ : Γ(Z, ⊤) →+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp η.appTop.hom
  have hφ : Function.Injective φ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).1.comp (appTop_injective η h)
  have hcomp : φ.comp ψ = algebraMap O Ω := by
    have : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ f.appTop ≫ η.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap O Ω) := by
      rw [← Scheme.Hom.comp_appTop_assoc, hf, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    exact congrArg (fun q => q.hom) this
  have hψ : ψ.IsIntegral :=
    RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2)
      (isIntegral_appTop_of_universallyClosed f)
  refine ⟨fun a b hab => hinj ?_, fun t => ?_⟩
  · rw [← hcomp]
    exact congrArg φ hab
  · have hi : IsIntegral O (φ t) := by
      obtain ⟨p, hp, e⟩ := hψ t
      refine ⟨p, hp, ?_⟩
      rw [← hcomp, ← Polynomial.hom_eval₂, e, map_zero]
    obtain ⟨o, ho⟩ := mem_range_of_isIntegral hinj hc _ hi
    refine ⟨o, hφ ?_⟩
    rw [← ho, ← hcomp]
    rfl

attribute [local instance] GroundTheory.Arith.SchemeCoh.algebraOfOver in
open GroundTheory.Arith.SchemeCoh in

theorem isConnected_closed {Z : Scheme.{0}} {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (f : Z ⟶ Spec (CommRingCat.of O)) [IsProper f]
    (h : Function.Bijective (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)) :
    _root_.IsConnected (f ⁻¹' {IsLocalRing.closedPoint O}) := by
  letI : Z.Over (Spec (.of O)) := ⟨f⟩
  have : IsProper (Z ↘ Spec (.of O)) := (inferInstance : IsProper f)
  exact isConnected_closedFibre_of_surj (A := O) (X := Z) h
    (fun x hx => formalFunctions_mem_range (IsLocalRing.maximalIdeal O) (isCoherent_unit Z) 0 hx 0)

end PositivityTheory.Xgn.SpecialFibreConnected

open PositivityTheory.Xgn.SpecialFibreConnected in
theorem PositivityTheory.Xgn.zero_set_special_fibre_connected : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ConstClosed O Ω → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨U, hU, hcl, hint⟩ := cpt_open_integral X Ω ξ hg
  have hrange : Set.range ξ ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint Ω := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    rw [Scheme.Opens.range_ι, hz]
    exact (hU _).2 specializes_rfl
  let η : Spec (CommRingCat.of Ω) ⟶ U.toScheme := IsOpenImmersion.lift U.ι ξ hrange
  have hη : η ≫ U.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by rwa [Scheme.Opens.range_ι])
  have hsp : ∀ q : U.toScheme, η (IsLocalRing.closedPoint Ω) ⤳ q := fun q => by
    rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff]
    have e : U.ι (η (IsLocalRing.closedPoint Ω)) = genPt ξ :=
      congrArg (fun g : Spec (CommRingCat.of Ω) ⟶ X => g (IsLocalRing.closedPoint Ω)) hη
    exact e ▸ (hU _).1 q.2
  have hb := bijective_const η hsp (U.ι ≫ s) hinj (by rw [← Category.assoc, hη, hs]) hc
  have hconn := (isConnected_closed (U.ι ≫ s) hb).image U.ι U.ι.continuous.continuousOn
  have hm : ∀ P : PrimeSpectrum O, ϖ ∈ P.asIdeal ↔ P = IsLocalRing.closedPoint O := fun P => by
    have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    constructor
    · intro h
      apply PrimeSpectrum.ext
      refine ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le P.isPrime.ne_top ?_).symm
      rw [hmax, Ideal.span_singleton_le_iff_mem]
      exact h
    · rintro rfl
      change ϖ ∈ IsLocalRing.maximalIdeal O
      rw [hmax]
      exact Ideal.mem_span_singleton_self ϖ
  have key : ∀ (q : X) (h : genPt ξ ⤳ q),
      ¬ unitAt ξ ⟨q, h⟩ (algebraMap O Ω ϖ) ↔ s q = IsLocalRing.closedPoint O := fun q h => by
    rw [(ConstReg.regular_const X Ω ξ O s hs ⟨q, h⟩ ϖ).2 hg, not_not]
    exact hm _
  convert hconn using 1
  ext q
  constructor
  · rintro ⟨h, hq⟩
    refine ⟨⟨q, (hU q).2 h⟩, ?_, rfl⟩
    exact (key q h).1 hq
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(hU _).1 z.2, (key _ _).2 hz⟩
