import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTotalSpaceIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectiveOverBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeOfSmoothOverNormalStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

namespace GlobalTheory.FlagEx

theorem main : ∀ (k : Type) [CommRing k] (B : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp k) (d : ℕ), IsArithVar q d →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B → ∀ (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ),
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
      IsFlagBundle π E r fl ∧ IsArithVar (π ≫ q) (d + ∑ a, r a * (r a - 1) / 2) ∧
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := by
  intro k _ B _ q d hq hB ι _ E r hE
  have := hq.isLocallyNoetherian
  have := hq.isNoetherianRing
  obtain ⟨Y, π, fl, hfl⟩ := GlobalTheory.T.exists_flag_bundle B ι E r hE
  have := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π ι E r fl hE hfl
  have hs := GlobalTheory.T.flag_bundle_projection_surjective B Y π ι E r fl hE hfl
  have := GlobalTheory.T.flag_bundle_total_space_irreducible B Y π ι E r fl hE hfl
  have hN := GlobalTheory.T.normal_scheme_of_smooth_over_normal B Y π (∑ a, r a * (r a - 1) / 2) hB
  have : IsReduced Y := by
    have : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y =>
      have := (hN y).1
      inferInstance
    exact isReduced_of_isReduced_stalk Y
  have hI : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  refine ⟨Y, hI, π, fl, hfl, ?_, hN⟩
  have := SmoothOfRelativeDimension.smooth (∑ a, r a * (r a - 1) / 2) π
  refine ⟨hq.isDomain, hq.finite, hI, GlobalTheory.T.flag_bundle_projective_over_base k B Y q π ι E r fl hq.isProjOver hE hfl, ?_, ?_⟩
  · rw [Category.assoc]
    have := hq.flat
    infer_instance
  · exact GlobalTheory.T.krull_dim_smooth_surjective_total B Y π _ d hs hq.dim_eq

end GlobalTheory.FlagEx
