import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_stalk_closed {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (U : X.Opens) (hp : p.1 ∈ U)
    (hη : genPt ξ ∈ U) (r : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp r) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη r) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := U) hp p.2
  have h2 := congr(($h).hom r)
  have e : ∀ x, genMap ξ p x =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes p.2).hom x) := fun _ => rfl
  rw [e]
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom h2

theorem stalk_eq_germ_div_of_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (b : X.presheaf.stalk x.1) :
    ∃ r t : Γ(X, U), b * X.presheaf.germ U x.1 x.2 t = X.presheaf.germ U x.1 x.2 r ∧
      IsUnit (X.presheaf.germ U x.1 x.2 t) := by
  have hl := hU.isLocalization_stalk x
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj (hU.primeIdealOf x).asIdeal.primeCompl b
  exact ⟨r, t.1, hrt, IsLocalization.map_units (X.presheaf.stalk x.1)
    (M := (hU.primeIdealOf x).asIdeal.primeCompl) t⟩

theorem regAt_isLocalRing_isFractionRing_stalk :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ →
      ∀ p : Cpt ξ, IsLocalRing (regAt ξ p) ∧ IsFractionRing (regAt ξ p) Ω ∧
        Nonempty (X.presheaf.stalk p.1 ≃+* regAt ξ p) := by
  intro X Ω _ ξ hξ p
  have hsurj : Function.Surjective (genMap ξ p).rangeRestrict := (genMap ξ p).rangeRestrict_surjective
  have hinj : Function.Injective (genMap ξ p).rangeRestrict := fun a b h =>
    hξ.inj p (congrArg Subtype.val h)
  have e : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
    RingEquiv.ofBijective (genMap ξ p).rangeRestrict ⟨hinj, hsurj⟩
  have hloc : IsLocalRing (regAt ξ p) :=
    IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict hsurj
  refine ⟨hloc, ?_, ⟨e⟩⟩
  apply IsFractionRing.of_field
  intro a
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := p.1) trivial
  have hη : genPt ξ ∈ U := p.2.mem_open U.2 hpU
  obtain ⟨b, rfl⟩ : ∃ b : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom b = a :=
    hξ.bij.2 a
  obtain ⟨r, t, hrt, hunit⟩ := stalk_eq_germ_div_of_affine hU ⟨genPt ξ, hη⟩ b
  replace hrt : b * X.presheaf.germ U (genPt ξ) hη t = X.presheaf.germ U (genPt ξ) hη r := hrt
  replace hunit : IsUnit (X.presheaf.germ U (genPt ξ) hη t) := hunit
  have hne : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη t) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨⟨_, X.presheaf.germ U p.1 hpU r, rfl⟩, ⟨_, X.presheaf.germ U p.1 hpU t, rfl⟩, ?_⟩
  show _ = genMap ξ p (X.presheaf.germ U p.1 hpU r) / genMap ξ p (X.presheaf.germ U p.1 hpU t)
  rw [genMap_germ_eq_stalk_closed ξ p U hpU hη, genMap_germ_eq_stalk_closed ξ p U hpU hη, eq_div_iff hne]
  exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans
    (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)

end GlobalTheory.CompanionTheory.Ar
