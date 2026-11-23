import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleFamilyUniqueIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTransportIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleLocallyFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFlagBundleSmoothRelativeDimStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
namespace GlobalTheory.FlagSmooth

theorem smooth_of_isFlagBundle : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules)
    (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) →
    IsFlagBundle π E r fl → SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) π := by
  intro B Y π ι _ E r fl hE hfl
  haveI : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2)) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  choose U hU hfree using GlobalTheory.T.vector_bundle_locally_free B ι E r hE
  have hcov : TopologicalSpace.IsOpenCover U :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hU x⟩
  refine IsZariskiLocalAtTarget.of_openCover (B.openCoverOfIsOpenCover U hcov) fun b => ?_
  change SmoothOfRelativeDimension _ (Limits.pullback.snd π (U b).ι)
  have h1 := GlobalTheory.T.flag_bundle_base_change B Y (U b) π ι E r fl hfl (U b).ι
  obtain ⟨Y0, π0, fl0, h0, hs⟩ := GlobalTheory.T.free_flag_bundle_smooth_relative_dim (U b) ι r
  obtain ⟨fl0', h0'⟩ := GlobalTheory.T.flag_bundle_transport_iso (U b) Y0 π0 ι _ (fun a => (Scheme.Modules.pullback (U b).ι).obj (E a)) r fl0 h0
    (fun a => ⟨(hfree b a).some.symm⟩)
  obtain ⟨e, he⟩ := GlobalTheory.T.flag_bundle_family_unique_iso (U b) Y0 _ π0 (Limits.pullback.snd π (U b).ι) ι _ r fl0' _ h0' h1
  have e' : Limits.pullback.snd π (U b).ι = e.inv ≫ π0 := by rw [← he, Iso.inv_hom_id_assoc]
  rw [e']
  first
    | exact (@MorphismProperty.cancel_left_of_respectsIso _ _ _ (HasRingHomProperty.respectsIso _) _ _ _ _ _).2 hs
    | exact (@MorphismProperty.cancel_left_of_respectsIso _ _ _ (IsZariskiLocalAtTarget.toRespectsIso) _ _ _ _ _).2 hs
    | (haveI : SmoothOfRelativeDimension 0 e.inv := inferInstance
       simpa using (inferInstance : SmoothOfRelativeDimension (0 + ∑ a, r a * (r a - 1) / 2) (e.inv ≫ π0)))

end GlobalTheory.FlagSmooth
