import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlueStatement

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem local_of_opens_pullback (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q] {X Y : Scheme.{0}}
    (f : X ⟶ Y) {Ix : Type} (V : Ix → Y.Opens) (hV : ∀ y : Y, ∃ i, y ∈ V i)
    (h : ∀ i, Q (pullback.snd f (V i).ι)) : Q f := by
  have hV' : iSup V = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 (hV y)
  exact IsZariskiLocalAtTarget.of_openCover (P := Q) (Y.openCoverOfIsOpenCover V hV') h

theorem Good.of_opens {g : ℕ} {X Y : Scheme.{0}} (f : X ⟶ Y) {Ix : Type} (V : Ix → Y.Opens)
    (hV : ∀ y : Y, ∃ i, y ∈ V i) (h : ∀ i, Good g (pullback.snd f (V i).ι)) : Good g f := by
  have h1 : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  have h2 : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  exact ⟨local_of_opens_pullback @IsProper f V hV fun i ↦ (h i).proper,
    local_of_opens_pullback (@SmoothOfRelativeDimension g) f V hV fun i ↦ (h i).smooth,
    local_of_opens_pullback @GeometricallyConnected f V hV fun i ↦ (h i).conn⟩

theorem hasRep_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (g : ℕ), IsAbelianScheme A → (∀ s : S, ∃ V : S.Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι)) → HasRep A g (𝟙_ _) := by
  intro S A _ g hA h
  choose V hV hR using h
  obtain ⟨B, P, hP, hG⟩ := GlobalTheory.T.exists_additiveFamily_representative_zariski_glue S A hA S V (fun _ ↦ g) (fun s ↦ ⟨s, hV s⟩) hR
  exact ⟨B, toUnit B, P, hP, Good.of_opens (Y := S) B.hom V (fun s ↦ ⟨s, hV s⟩) hG⟩

end GlobalTheory.DualCon
