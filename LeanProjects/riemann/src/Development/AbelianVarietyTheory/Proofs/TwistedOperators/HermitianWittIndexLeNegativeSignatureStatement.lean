import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianWittIndexLeNegativeSignature
import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWittIndex_le_negative_signature : ∀ {D : D7} (M : HSp D) {p : ℕ} {τ : D.what₂.Tau}, Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p → ∀ {r : ℕ} {Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E}, GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf → r ≤ p := by
  first | exact @GlobalTheory.WittSig.wittIndex_le_neg | exact GlobalTheory.WittSig.wittIndex_le_neg | (intros; apply GlobalTheory.WittSig.wittIndex_le_neg <;> assumption)
