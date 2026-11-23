import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LipschitzBoundRealUnipotentAction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lipschitz_bound_real_unipotent_action : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (φ : GA D V → ℂ) (c : ℝ), 0 ≤ c → Lip θ A φ c → ∀ (u : (Formalism.IndefR.Eqv.UI.instV fr).Ginf) (Av Z : InfinitePlace D.host.F → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ v, Formalism.REAL.inG (fr.ε v) (Av v) ∧ Formalism.REAL.inG (fr.ε v) (Z v)) → (∀ v, Formalism.MainNotions.S.uMat (u v) = NormedSpace.exp (Av v) * NormedSpace.exp (Z v)) → ∀ y : GA D V, ‖φ (y * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) - φ y‖ ≤ c * ∑ v, (Real.sqrt (Formalism.REAL.hs (Av v)) + Real.sqrt (Formalism.REAL.hs (Z v))) := by
  first | exact @GlobalTheory.RealMove.lip_move_real | exact GlobalTheory.RealMove.lip_move_real | (intros; apply GlobalTheory.RealMove.lip_move_real <;> assumption)
