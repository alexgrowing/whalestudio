import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

namespace GlobalTheory

theorem spec_hom_ext_of_span_eq_top : ∀ {L : Type} [CommRing L] {s : Set L}, Ideal.span s = ⊤ → ∀ {Y : Scheme.{0}} {w w' : Sp L ⟶ Y}, (∀ a : s, spMap (algebraMap L (Localization.Away (a : L))) ≫ w = spMap (algebraMap L (Localization.Away (a : L))) ≫ w') → w = w' := by
  intro L _ s hs Y w w' h
  have hs' : Ideal.span (Set.range (Subtype.val : s → L)) = ⊤ := by
    rw [Subtype.range_coe]; exact hs
  exact (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of L) (Subtype.val : s → L) hs').openCover.hom_ext _ _ h

end GlobalTheory
