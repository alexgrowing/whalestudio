import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory

universe u

open TensorProduct in

theorem ringHom_formallyUnramified_of_comp_faithfullyFlat {A B C : Type*} [CommRing A]
    [CommRing B] [CommRing C] {φ : A →+* B} {β : B →+* C} (hβ : β.FaithfullyFlat)
    (hs : β.FormallySmooth) (hu : β.FormallyUnramified) (h : (β.comp φ).FormallyUnramified) :
    φ.FormallyUnramified := by
  algebraize [φ, β, β.comp φ]
  have : Algebra.FormallyEtale B C :=
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  have h1 : Subsingleton (C ⊗[B] Ω[B⁄A]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B C).subsingleton
  exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right B C).mp h1⟩

theorem faithfullyFlat_stalkMap_of_flat {W X : Scheme.{u}} (g : W ⟶ X) [Flat g] (w : W) :
    (g.stalkMap w).hom.FaithfullyFlat := by
  have h := Flat.stalkMap g w
  algebraize [(g.stalkMap w).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (g w)) (W.presheaf.stalk w)) :=
    inferInstanceAs <| IsLocalHom (g.stalkMap w).hom
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem flat_of_comp_of_flat_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X) (u : X ⟶ Y)
    [Flat g] [Surjective g] [Flat (g ≫ u)] : Flat u := by
  refine Flat.of_stalkMap u fun x => ?_
  obtain ⟨w, rfl⟩ := g.surjective x
  have h := Flat.stalkMap (g ≫ u) w
  rw [Scheme.Hom.stalkMap_comp] at h
  exact ringHom_flat_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w) h

theorem formallyUnramified_of_comp_of_etale_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X)
    (u : X ⟶ Y) [Etale g] [Surjective g] [FormallyUnramified (g ≫ u)] :
    FormallyUnramified u := by
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  refine HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime fun x => ?_
  obtain ⟨w, rfl⟩ := g.surjective x
  have h := FormallyUnramified.stalkMap (g ≫ u) w
  rw [Scheme.Hom.stalkMap_comp] at h
  have hs : (g.stalkMap w).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (g.smoothLocus_eq_top.ge (Set.mem_univ w))
  exact ringHom_formallyUnramified_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w)
    hs (FormallyUnramified.stalkMap g w) h

theorem etale_of_comp_of_etale_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X)
    (u : X ⟶ Y) [Etale g] [Surjective g] [Etale (g ≫ u)] [LocallyOfFinitePresentation u] :
    Etale u := by
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  have : Flat (g ≫ u) := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale (g ≫ u)›).1
  have := flat_of_comp_of_flat_of_surjective g u
  have := formallyUnramified_of_comp_of_etale_of_surjective g u
  exact Etale.of_formallyUnramified_of_flat u

theorem exists_opens_range_etale_of_comp :
    ∀ (W X Y : Scheme.{0}) (g : W ⟶ X) (u : X ⟶ Y) [Etale g] [Etale (g ≫ u)]
      [LocallyOfFinitePresentation u],
      ∃ V : X.Opens, (V : Set X) = Set.range g ∧ Etale (V.ι ≫ u) := by
  intro W X Y g u _ _ _
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  let V : X.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  refine ⟨V, rfl, ?_⟩
  have hr : Set.range g ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]; exact subset_rfl
  let g' : W ⟶ V := IsOpenImmersion.lift V.ι g hr
  have hg' : g' ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have : Etale (g' ≫ V.ι) := by rw [hg']; infer_instance
  have : Etale g' := Etale.of_comp g' V.ι
  have : Surjective g' := by
    refine ⟨fun v => ?_⟩
    obtain ⟨w, hw⟩ : V.ι v ∈ Set.range g := v.2
    refine ⟨w, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg', hw]
  have : Etale (g' ≫ V.ι ≫ u) := by rw [← Category.assoc, hg']; infer_instance
  exact etale_of_comp_of_etale_of_surjective g' (V.ι ≫ u)

end GlobalTheory
