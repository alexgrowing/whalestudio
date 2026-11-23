import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableDiagonalModSmall
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairingTable_diagonal_modSmall : ∀ {M A : Type} [Zero M] [Ring A] (p : M → M → A) (sm : A → Prop) (ρ k n : ℕ), n = 2 * ρ + k + 1 → ∀ (e f : Fin ρ → M) (b b' : Fin k → M) (z : M), PairTable p sm e f b b' z → ∀ a c : Fin n, sm (p (flagV ρ k n f e b' z a) (flagV ρ k n e f b z c) - if a = c then sgnD ρ k a else 0) := by
  first | exact @GlobalTheory.SeeConjRead.flagV_pair_table | exact GlobalTheory.SeeConjRead.flagV_pair_table | (intros; apply GlobalTheory.SeeConjRead.flagV_pair_table <;> assumption)
