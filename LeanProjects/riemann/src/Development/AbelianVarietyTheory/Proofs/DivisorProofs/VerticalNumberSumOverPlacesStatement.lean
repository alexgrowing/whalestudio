import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalNumberSumOverPlaces
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLgOfLnSymUpdateSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.LocM
open GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open GlobalTheory.PairTerm
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_number_sum_over_places : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (Y : Var D.what₂.LL) (V : Cover Y) (n : ℕ) (N : Fin n → HermLB V.p)
    (g : V.X → ℝ), (Function.support g).Finite →
    ∑ᶠ y, g y * vertNum p V n N y = (letI := Formalism.L2.Geo.finPl D p;
      ∑ la : Formalism.L2.Geo.PlL D p, ∑ᶠ y, if LiesOverPl V la.1 y then g y * vertNum p V n N y else 0) := by
  first | exact @GlobalTheory.PairTerm.finsum_vertNum_eq_sum_places | exact GlobalTheory.PairTerm.finsum_vertNum_eq_sum_places | (intros; apply GlobalTheory.PairTerm.finsum_vertNum_eq_sum_places <;> assumption)
