import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricCombEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyGradedLinesIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreeEqFlagDegreeStatement

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.CovTest.SwapZ

theorem swapEq_flagZ : Hypotheses2 → GlobalTheory.Published.ArDegree → ∀ G, Homog G → SwapFl G → ∀ (D : D7) (Y : DV.ShimX D.what₂.Tau) (hh : Fn Y), GlobalTheory.FlagZ.IsHh D.what₂.Tau Y.N hh → SwapEq Y G hh (degFl D.what₂.Tau Y.N) :=
  fun hP hA G _ hG D Y hh H => swap_of_model GlobalTheory.T.flag_variety_graded_lines_isometric (GlobalTheory.T.generic_degree_eq_flag_degree hP hA) G hG D Y hh H

end GlobalTheory.CovTest.SwapZ
