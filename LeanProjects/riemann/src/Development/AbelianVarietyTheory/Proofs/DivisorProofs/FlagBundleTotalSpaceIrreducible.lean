import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsAfterBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleOverFieldIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleUniversallyOpenStatement

set_option autoImplicit false

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

namespace GlobalTheory.CovTest

theorem IsFlagBundle.geometricallyIrreducible {B Y : Scheme.{0}} {π : Y ⟶ B} {ι : Type} [Fintype ι] {E : ι → B.Modules}
    {r : ι → ℕ} {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)} (hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a))
    (hF : IsFlagBundle π E r fl) : GeometricallyIrreducible π := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  obtain ⟨fl', h'⟩ := GlobalTheory.T.flag_bundle_exists_after_base_change B Y _ π x ι E r fl hF
  exact GlobalTheory.T.flag_bundle_over_field_irreducible K _ (pullback.snd π x) ι _ r fl' (fun a => (hE a).pullback x) h'

theorem IsFlagBundle.irreducibleSpace : ∀ (B Y : Scheme.{0}) [IsIntegral B] [IsLocallyNoetherian B] (π : Y ⟶ B) (ι : Type)
    [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IrreducibleSpace Y := by
  intro B Y _ _ π ι _ E r fl hE hF
  have := hF.geometricallyIrreducible hE
  have := GlobalTheory.T.flag_bundle_universally_open B Y π ι E r fl hE hF
  exact GeometricallyIrreducible.irreducibleSpace π π.isOpenMap

end GlobalTheory.CovTest
