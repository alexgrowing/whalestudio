import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSOfIdToRingHom
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

namespace GlobalTheory.ArLieBase

set_option backward.isDefEq.respectTransparency false in

theorem hom_ext_dualNumber_away : ∀ {L : Type} [CommRing L] {s : Set L}, Ideal.span s = ⊤ → ∀ {Y : Scheme.{0}} {w w' : Sp (DualNumber L) ⟶ Y}, (∀ a : s, spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w = spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w') → w = w' := by
  intro L _ s hs Y w w' h
  have hs' : Ideal.span (Set.range (fun k : s => (TrivSqZeroExt.inl (k : L) : DualNumber L))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom L L)) hs
    rw [Ideal.map_span, Ideal.map_top, Set.image_eq_range] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber L)) _ hs').openCover
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : s) => ?_
  have hd : Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (k : L))) =
      ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L) := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  have e : 𝒰.f k = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.toL (k : L))) ≫
      Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ReciprocityTheory.ChartRestriction.G.Chart.toL_comp]
    rfl
  have hk := h k
  rw [hd] at hk
  rw [e, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) hk

end GlobalTheory.ArLieBase
