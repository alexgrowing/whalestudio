import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.CovSz

theorem covers_and
    {Q Q' : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : Covers fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP)
    (h' : Covers fun Fm x hx ι p i Y PP _ => Q' Fm x hx ι p i Y PP) :
    Covers fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP ∧ Q' Fm x hx ι p i Y PP := by
  refine (Formalism.MainNotions.Closed.and h h').imp fun Fm CH _ hh => ?_
  obtain ⟨⟨C, hC, a, ha⟩, ⟨C', hC', b, hb⟩⟩ := hh
  exact ⟨C, hC, max a b, fun x hx hle ι p hp i hi Y hY =>
    ⟨ha x hx ((le_max_left _ _).trans hle) ι p hp i hi Y hY, hb x hx ((le_max_right _ _).trans hle) ι p hp i hi Y hY⟩⟩

theorem covers_of_lifts
    {P : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (PP C : ℝ), Prop}
    {Q : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : Lifts P)
    (hQ : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (C : ℝ), RowsT p → P Fm x hx ι p i (Fm.parT x hx ι).PP C → (i : ℕ) + 1 < (Fm.D x ι).R.m →
      ∀ Y : Cov p i, GoodCov p i Y → Q Fm x hx ι p i Y (Fm.parT x hx ι).PP) :
    Covers fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP := by
  refine h.imp fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY => hQ Fm x hx ι p i C hp (ha x hx hle ι p hp i) hi Y hY⟩

theorem covers_imp
    {Q R : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : Covers fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP)
    (hQ : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (Y : Cov p i) (PP : ℝ), Q Fm x hx ι p i Y PP → R Fm x hx ι p i Y PP) :
    Covers fun Fm x hx ι p i Y PP _ => R Fm x hx ι p i Y PP := by
  refine h.imp fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY => hQ Fm x hx ι p i Y _ (ha x hx hle ι p hp i hi Y hY)⟩

end GlobalTheory.CovTop.CovSz

end
