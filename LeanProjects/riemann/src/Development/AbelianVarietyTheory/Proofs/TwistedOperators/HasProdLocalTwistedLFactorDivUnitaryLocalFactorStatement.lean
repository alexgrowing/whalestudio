import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasProdLocalTwistedLFactorDivUnitaryLocalFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProd_localTwistedLFactor_div_unitaryLocalFactor : ∀ (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : Fam D.host.E) (χ : (AE D)ˣ →* Circle), Converges (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist B (val χ)⁻¹) ((1 + (D.R.t : ℂ)) / 2) → HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => LvTw B (val χ) v.1 ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v.1 : ℂ)) (LSD D Sb B χ ((1 + (D.R.t : ℂ)) / 2) / (dOff D Sb : ℂ)) := by
  first | exact @GlobalTheory.FinZeta.hasProd_LvTw_div_dLoc | exact GlobalTheory.FinZeta.hasProd_LvTw_div_dLoc | (intros; apply GlobalTheory.FinZeta.hasProd_LvTw_div_dLoc <;> assumption)
