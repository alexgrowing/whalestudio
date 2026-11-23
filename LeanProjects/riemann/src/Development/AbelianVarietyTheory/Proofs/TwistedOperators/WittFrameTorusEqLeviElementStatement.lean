import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElement
import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittFrame_torus_eq_levi_element : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (M : HSp D) (r : ℕ)
    (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf →
    ∃ (S₀ : HSp D) (d : GlobalTheory.MixModel.HypDec (sgn ε M) S₀ r), ∀ t : Fin r → ℝ, (∀ i, 0 < t i) →
      ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
        ∃ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 ∧
          (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) ∧ (ofSgn ε M).symm a = d.levi α := by
  first | exact @GlobalTheory.WittLevi.witt_levi | exact GlobalTheory.WittLevi.witt_levi | (intros; apply GlobalTheory.WittLevi.witt_levi <;> assumption)
