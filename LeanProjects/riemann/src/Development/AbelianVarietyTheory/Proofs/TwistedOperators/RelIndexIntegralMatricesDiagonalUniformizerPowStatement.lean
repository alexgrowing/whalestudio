import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesDiagonalUniformizerPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_integralMatrices_diagonal_uniformizer_pow : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (Q : ℕ), ϖ ≠ 0 → Valued.v ϖ ≤ 1 → (∀ e : ℕ, ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex (Formalism.UG.intL L).toAddSubgroup = Q ^ e) → ∀ (r n : ℕ) (d : Fin r → ℤ), (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (Matrix.diagonal (fun i => ϖ ^ d i)))) = Q ^ (n * (∑ i, max (-d i) 0).toNat) := by
  first | exact @GlobalTheory.DiagIdx.relIndex_intMat_diag | exact GlobalTheory.DiagIdx.relIndex_intMat_diag | (intros; apply GlobalTheory.DiagIdx.relIndex_intMat_diag <;> assumption)
