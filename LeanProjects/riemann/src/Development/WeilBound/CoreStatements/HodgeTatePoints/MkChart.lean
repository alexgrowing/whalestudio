import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGenericStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace PositivityTheory.HtPt.Mk

theorem gen_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  obtain ⟨q, hq⟩ := p
  have a := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hq
  have b := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have c : Spec.map (CommRingCat.ofHom (genMap ξ ⟨q, hq⟩)) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes hq) :=
    Spec.map_comp _ _
  rw [c, Category.assoc]
  exact (congrArg (fun m => Spec.map (Scheme.stalkClosedPointTo ξ) ≫ m) a).trans b

theorem stalk_normal₀ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    (hN : Flat.NormalCpt ξ) (q : Cpt ξ) : ∃ (_ : IsDomain (X.presheaf.stalk q.1)),
      IsIntegrallyClosed (X.presheaf.stalk q.1) ∧ ∃ κ : FractionRing (X.presheaf.stalk q.1) ≃+* Ω,
        κ.toRingHom.comp (algebraMap _ _) = genMap ξ q := by
  have hd : IsDomain (X.presheaf.stalk q.1) := (hξ.inj q).isDomain _
  letI : Algebra (X.presheaf.stalk q.1) Ω := (genMap ξ q).toAlgebra
  have : FaithfulSMul (X.presheaf.stalk q.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 (hξ.inj q)
  have hf : IsFractionRing (X.presheaf.stalk q.1) Ω := by
    refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨b, c, hc, e⟩ := GlobalTheory.T.exists_stalk_fraction_of_generic ξ hξ q a
    exact ⟨b, c, (eq_div_iff hc).2 e⟩
  refine ⟨hd, ?_, (FractionRing.algEquiv _ Ω).toRingEquiv, RingHom.ext (FractionRing.algEquiv _ Ω).commutes⟩
  rw [isIntegrallyClosed_iff Ω]
  intro a ha
  exact hN q a (IsIntegral.map_of_comp_eq (genMap ξ q).rangeRestrict (RingHom.id Ω) (RingHom.ext fun _ => rfl) ha)

theorem ht_lat_chart : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ q : Cpt ξ, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (x : Spec (CommRingCat.of R) ⟶ X) (κ : FractionRing R ≃+* Ω), IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsOpenImmersion x ∧ q.1 ∈ Set.range x ∧ (∀ y ∈ Set.range x, genPt ξ ⤳ y) ∧ spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x = ξ := by
  intro X _ Ω _ _ ξ hξ hN q
  obtain ⟨U, hqU, hU, hinj⟩ := X.exists_germ_injective q.1
  let k₀ : Γ(X, U) →+* Ω := (genMap ξ q).comp (X.presheaf.germ U q.1 hqU).hom
  have hk : Function.Injective k₀ := (hξ.inj q).comp hinj
  have hd : IsDomain Γ(X, U) := hk.isDomain _
  have hx : Spec.map (CommRingCat.ofHom k₀) ≫ hU.fromSpec = ξ := by
    refine Eq.trans ?_ (gen_stalk ξ q)
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hqU, IsAffineOpen.fromSpecStalk, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hall : ∀ p : Spec Γ(X, U), genPt ξ ⤳ hU.fromSpec p := by
    intro p
    have e : genPt ξ = hU.fromSpec (Spec.map (CommRingCat.ofHom k₀) (IsLocalRing.closedPoint Ω)) := by
      rw [← hx]; rfl
    rw [e]
    refine Specializes.map ?_ hU.fromSpec.continuous
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
    have h1 : k₀ a ∈ IsLocalRing.maximalIdeal Ω := ha
    rw [IsLocalRing.maximalIdeal_eq_bot] at h1
    rw [hk (h1.trans (map_zero k₀).symm)]
    exact Ideal.zero_mem _
  letI : Algebra Γ(X, U) Ω := k₀.toAlgebra
  have : FaithfulSMul Γ(X, U) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hk
  have hf : IsFractionRing Γ(X, U) Ω := by
    refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨b, c, hc, e⟩ := GlobalTheory.T.exists_stalk_fraction_of_generic ξ hξ q a
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨q.1, hqU⟩ : U)
    have hl := hU.isLocalization_stalk ⟨q.1, hqU⟩
    obtain ⟨⟨b₁, s⟩, hb⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hqU⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) b
    obtain ⟨⟨c₁, t⟩, hc'⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hqU⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) c
    have hb' : genMap ξ q b * k₀ s = k₀ b₁ := by
      have := congrArg (genMap ξ q) hb
      rwa [map_mul] at this
    have hc'' : genMap ξ q c * k₀ t = k₀ c₁ := by
      have := congrArg (genMap ξ q) hc'
      rwa [map_mul] at this
    have hne : ∀ s : (hU.primeIdealOf ⟨q.1, hqU⟩).asIdeal.primeCompl, k₀ s ≠ 0 := fun s h =>
      s.2 (by rw [hk (h.trans (map_zero k₀).symm)]; exact Ideal.zero_mem _)
    refine ⟨b₁ * t, c₁ * s, ?_⟩
    change a = k₀ (b₁ * t) / k₀ (c₁ * s)
    rw [map_mul, map_mul, ← hb', ← hc'', ← e, eq_div_iff (mul_ne_zero (mul_ne_zero hc (hne t)) (hne s))]
    ring
  refine ⟨Γ(X, U), inferInstance, hd, hU.fromSpec, (FractionRing.algEquiv _ Ω).toRingEquiv,
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩, ?_, inferInstance, ?_, ?_, ?_⟩
  · refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
    let P : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec P ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨P, rfl⟩
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨_, hy⟩ : U)
    have hl : IsLocalization p.primeCompl (X.presheaf.stalk (hU.fromSpec P)) := hU.isLocalization_stalk' P hy
    obtain ⟨_, hic, -⟩ := stalk_normal₀ hξ hN ⟨_, hall P⟩
    exact IsIntegrallyClosed.of_equiv (R := X.presheaf.stalk (hU.fromSpec P))
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (hU.fromSpec P)) (Localization.AtPrime p)).toRingEquiv
  · rw [hU.range_fromSpec]
    exact hqU
  · rintro _ ⟨p, rfl⟩
    exact hall p
  · have e : (FractionRing.algEquiv Γ(X, U) Ω).toRingEquiv.toRingHom.comp (algebraMap _ _) = k₀ :=
      RingHom.ext (FractionRing.algEquiv _ Ω).commutes
    rw [e]
    exact hx

end PositivityTheory.HtPt.Mk
