import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteSplitTorusExtensionOfTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem geometricallyConnected_of_generic_of_special (W L : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] {X : Scheme.{0}} (f : X ⟶ Sp W)
    (h₁ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W L))))
    (h₂ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W (IsLocalRing.ResidueField W))))) :
    GeometricallyConnected f := by
  have key : ∀ (Ω F : Type) [Field Ω] [Field F] (a : W →+* F) (ψ : F →+* Ω),
      GeometricallyConnected (pullback.snd f (spMap a)) →
      ∀ (Z : Scheme.{0}) (fst : Z ⟶ X) (snd : Z ⟶ Sp Ω), IsPullback fst snd f (spMap (ψ.comp a)) →
      ConnectedSpace Z := by
    intro Ω F _ _ a ψ h Z fst snd hZ
    have e : spMap (ψ.comp a) = spMap ψ ≫ spMap a := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e] at hZ
    have sq : IsPullback (pullback.lift fst (snd ≫ spMap ψ) (hZ.w.trans (Category.assoc _ _ _).symm)) snd
        (pullback.snd f (spMap a)) (spMap ψ) :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact hZ) (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback f (spMap a))
    exact GeometricallyConnected.geometrically_connectedSpace (f := pullback.snd f (spMap a)) _ _ _ sq
  refine ⟨fun Ω _ q Z fst snd hZ => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  change IsPullback fst snd f (spMap φ.hom) at hZ
  by_cases h : RingHom.ker φ.hom = ⊥
  · have hinj := (RingHom.injective_iff_ker_eq_bot _).2 h
    have e : (IsFractionRing.lift (K := L) hinj).comp (algebraMap W L) = φ.hom :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    rw [← e] at hZ
    exact key Ω L _ _ h₁ Z fst snd hZ
  · have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal h)
    let ψ : IsLocalRing.ResidueField W →+* Ω :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ.hom fun a ha => (RingHom.mem_ker).1 (hm ▸ ha)
    have e : ψ.comp (algebraMap W (IsLocalRing.ResidueField W)) = φ.hom := RingHom.ext fun x => rfl
    rw [← e] at hZ
    exact key Ω _ _ _ h₂ Z fst snd hZ

theorem isSemiAbelian_of_abelian_generic_of_torusExt : NfSt := by
  intro W _ _ _ L _ _ _ A _ hA G _ hc hs hsep hqc ⟨e, _⟩ hT
  obtain ⟨k, _, _, _, ⟨E⟩⟩ := GlobalTheory.T.exists_finite_splitTorusExtension_of_torusExtension _ _ hT
  have hw : (baseChange W L G).hom = e.hom.left ≫ A.hom := (Over.w e.hom).symm
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have := hA.proper
  have := hA.geomConnected
  have hp : IsProper (baseChange W L G).hom := by rw [hw]; infer_instance
  have hg : GeometricallyConnected (baseChange W L G).hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨by rw [hw, Category.comp_id]⟩) hA.geomConnected
  have hk := (GlobalTheory.torusExtension_smooth_geometricallyConnected _ E).2.2.2.1
  have hsurj : Surjective (spMap (algebraMap (IsLocalRing.ResidueField W) k)) :=
    ⟨fun z => ⟨_, Subsingleton.elim (spMap (algebraMap (IsLocalRing.ResidueField W) k)
      (default : PrimeSpectrum _)) z⟩⟩
  have hsp : GeometricallyConnected (specialFibre W G).hom :=
    @GlobalTheory.geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _
      (IsPullback.of_hasPullback (specialFibre W G).hom (spMap (algebraMap (IsLocalRing.ResidueField W) k)))
      hsurj hk
  have hgc : GeometricallyConnected G.hom := geometricallyConnected_of_generic_of_special W L G.hom hg hsp
  refine isSemiAbelian_of_proper_generic_of_torusExtension W L G ⟨hc, hs, hsep, hqc, hgc⟩ hp k
    ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) ?_ ?_ ?_
  · rw [RingHom.ker_comp_of_injective _ (algebraMap (IsLocalRing.ResidueField W) k).injective]
    exact IsLocalRing.ker_residue
  · refine RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective) ?_
    exact Algebra.IsIntegral.isIntegral
  · have e' : spMap ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) =
        spMap (algebraMap (IsLocalRing.ResidueField W) k) ≫ spMap (algebraMap W (IsLocalRing.ResidueField W)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e']
    have : IsMonHom (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso _ _ G).inv)
    exact ⟨torusExtOfIso (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm E⟩

end GlobalTheory.SS
