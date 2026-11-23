import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagSmoothArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellVarietyDimensionCounts
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

namespace GlobalTheory.FlagQ

theorem smoothOfRelativeDimension_genericFibre (ι : Type) [Fintype ι] (N : ℕ) :
    SmoothOfRelativeDimension (dimFl ι N) (pullback.snd (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ))) := by
  have h := (GlobalTheory.FlagZ.smooth_dim_isArithVar_part ι (ι × Fin (N + 1)) N Prod.fst Prod.snd).1
  rw [(GlobalTheory.FlagZ.Count.card_cellVar ι N).1] at h
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_hasPullback (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ))) h

end GlobalTheory.FlagQ
