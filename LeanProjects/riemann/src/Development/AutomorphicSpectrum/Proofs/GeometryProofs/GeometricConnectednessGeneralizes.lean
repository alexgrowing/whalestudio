import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyIntegralFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpaceOfIsFieldGlobalFunctions
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_isPullback_left {P Q X S T U : Scheme.{0}} {t : P ⟶ X} {v : P ⟶ U} {p : X ⟶ S}
    {g : U ⟶ T} {f : T ⟶ S} {t' : Q ⟶ X} {v' : Q ⟶ T}
    (h : IsPullback t v p (g ≫ f)) (h' : IsPullback t' v' p f) :
    ∃ u : P ⟶ Q, IsPullback u v v' g := by
  refine ⟨h'.lift t (v ≫ g) (by simpa using h.w), ?_⟩
  refine IsPullback.of_right (h₁₂ := t') (h₂₂ := f) (v₁₃ := p) ?_ (by simp) h'
  simpa using h

theorem spMap_comp_spMap {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem geometricallyConnected_of_local {k A E L K : Type} [CommRing k] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Field E] [Field L] [Field K] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (e : Sp k ⟶ X) (hs : e ≫ p = 𝟙 _) [Smooth p] [IsProper p] (φ : k →+* A) (a : k →+* E)
    (b : E →+* IsLocalRing.ResidueField A)
    (hb : b.comp a = (IsLocalRing.residue A).comp φ)
    (hE : GeometricallyConnected (pullback.snd p (spMap a)))
    (j : A →+* L) (hj : j.Flat) (c : k →+* K) (d : K →+* L) (hd : d.comp c = j.comp φ) :
    GeometricallyConnected (pullback.snd p (spMap c)) := by
  have hPA : IsPullback (pullback.fst p (spMap φ)) (pullback.snd p (spMap φ)) p (spMap φ) :=
    .of_hasPullback _ _
  haveI : Smooth (pullback.snd p (spMap φ)) := MorphismProperty.of_isPullback hPA ‹_›
  haveI : IsProper (pullback.snd p (spMap φ)) := MorphismProperty.of_isPullback hPA ‹_›
  haveI : Flat (pullback.snd p (spMap φ)) := inferInstance
  let eA : Sp A ⟶ pullback p (spMap φ) :=
    pullback.lift (spMap φ ≫ e) (𝟙 _) (by rw [Category.assoc, hs]; simp)
  have heA : eA ≫ pullback.snd p (spMap φ) = 𝟙 _ := pullback.lift_snd _ _ _

  have hW : IsPullback (pullback.fst (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)))
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)))
      (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)) := .of_hasPullback _ _
  have hbot : spMap (IsLocalRing.residue A) ≫ spMap φ = spMap b ≫ spMap a := by
    rw [spMap_comp_spMap, spMap_comp_spMap, hb]
  have hW' := hW.paste_horiz hPA
  rw [hbot] at hW'
  obtain ⟨u, hu⟩ := exists_isPullback_left hW' (.of_hasPullback p (spMap a))
  haveI : Smooth (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    MorphismProperty.of_isPullback hW ‹_›
  haveI : GeometricallyConnected
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    MorphismProperty.of_isPullback hu hE
  have hGI : GeometricallyIntegral
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    GlobalTheory.geometricallyIntegral_of_smooth _
  haveI hA : IsIso (pullback.snd p (spMap φ)).appTop :=
    isIso_appTop_of_closedFibre A _ _ eA heA inferInstance inferInstance hGI

  have hL : IsPullback (pullback.fst (pullback.snd p (spMap φ)) (spMap j))
      (pullback.snd (pullback.snd p (spMap φ)) (spMap j))
      (pullback.snd p (spMap φ)) (spMap j) := .of_hasPullback _ _
  haveI : Flat (spMap j) := Flat.SpecMap_iff.2 hj
  haveI hL1 : IsIso (pullback.snd (pullback.snd p (spMap φ)) (spMap j)).appTop :=
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback hL
  have hbot' : spMap j ≫ spMap φ = spMap d ≫ spMap c := by
    rw [spMap_comp_spMap, spMap_comp_spMap, hd]
  have hL' := hL.paste_horiz hPA
  rw [hbot'] at hL'
  obtain ⟨w, hw⟩ := exists_isPullback_left hL' (.of_hasPullback p (spMap c))
  haveI : Flat (spMap d) := Flat.SpecMap_iff.2 (by
    algebraize [d]
    exact RingHom.flat_algebraMap_iff.2 inferInstance)
  haveI : Surjective (spMap d) := by
    refine ⟨fun x => ?_⟩
    have y : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
    exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  haveI hK : IsIso (pullback.snd p (spMap c)).appTop :=
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback_of_surjective hw
  exact geometricallyConnected_of_isIso_appTop K _ _ inferInstance inferInstance hK

theorem geometricallyConnected_of_localDomain {k B A E K : Type} [CommRing k] [CommRing B]
    [IsDomain B] [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Field E] [Field K]
    [Algebra B K] [IsFractionRing B K] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (e : Sp k ⟶ X) (hs : e ≫ p = 𝟙 _) [Smooth p] [IsProper p] (q : k →+* B) (ψ : B →+* A)
    (hψ : Function.Injective ψ) (a : k →+* E) (b : E →+* IsLocalRing.ResidueField A)
    (hb : b.comp a = (IsLocalRing.residue A).comp (ψ.comp q))
    (hE : GeometricallyConnected (pullback.snd p (spMap a))) :
    GeometricallyConnected (pullback.snd p (spMap ((algebraMap B K).comp q))) := by
  have hinj : Function.Injective ((algebraMap A (FractionRing A)).comp ψ) :=
    (IsFractionRing.injective A (FractionRing A)).comp hψ
  refine geometricallyConnected_of_local (A := A) (E := E) (L := FractionRing A) X p e hs (ψ.comp q)
    a b hb hE (algebraMap A (FractionRing A)) (RingHom.flat_algebraMap_iff.2 inferInstance) _
    (IsFractionRing.lift hinj) ?_
  ext r
  simp only [RingHom.comp_apply]
  exact IsFractionRing.lift_algebraMap hinj (q r)

theorem stableUnderGeneralization_geometricallyConnected_fibre :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
      (e : Sp k ⟶ X), e ≫ p = 𝟙 _ → Smooth p → IsProper p →
      StableUnderGeneralization {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ X p e hs _ _ x y hyx hx
  have hle : y.asIdeal ≤ x.asIdeal := (PrimeSpectrum.le_iff_specializes y x).2 hyx
  have hq : Function.Surjective (Ideal.Quotient.mk y.asIdeal) := Ideal.Quotient.mk_surjective
  obtain ⟨Q, hQ, hcomap⟩ : ∃ Q : Ideal (k ⧸ y.asIdeal), ∃ _ : Q.IsPrime,
      x.asIdeal = Q.comap (Ideal.Quotient.mk y.asIdeal) := by
    refine ⟨x.asIdeal.map (Ideal.Quotient.mk y.asIdeal),
      Ideal.map_isPrime_of_surjective hq (by rw [Ideal.mk_ker]; exact hle), ?_⟩
    rw [Ideal.comap_map_of_surjective _ hq, eq_comm, sup_eq_left]
    refine le_trans ?_ hle
    rw [show Ideal.comap (Ideal.Quotient.mk y.asIdeal) ⊥ = RingHom.ker (Ideal.Quotient.mk y.asIdeal)
      from rfl, Ideal.mk_ker]
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : IsDomain (Localization.AtPrime Q) :=
    IsLocalization.isDomain_localization Q.primeCompl_le_nonZeroDivisors
  have := geometricallyConnected_of_localDomain (K := y.asIdeal.ResidueField) X p e hs
    (Ideal.Quotient.mk y.asIdeal) (algebraMap (k ⧸ y.asIdeal) (Localization.AtPrime Q))
    (IsLocalization.injective _ Q.primeCompl_le_nonZeroDivisors)
    (algebraMap k x.asIdeal.ResidueField)
    (Ideal.ResidueField.map x.asIdeal Q (Ideal.Quotient.mk y.asIdeal) hcomap)
    (by
      ext r
      simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
      rfl) hx
  exact this

end GlobalTheory.CompanionTheory.Ar.Approx
