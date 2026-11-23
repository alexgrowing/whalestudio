import Formalism.SharpRestriction.GlobalSchurBounds.LossesSmallShares
import Formalism.LocalToGlobal.GlobalTheory.SuppSat
import Formalism.SizeWindowBrackets.PrimeClassLossHypothesesSatisfiable

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss7

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds Formalism.LFunctionChainParameters.SmallOrderPrimeLosses Formalism.L2.GlobalTheoryTheory.Loss

def LossSettingFamily : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (X : G.Inst D L) (K : G.Consts) (Cr C bo : ℝ) (P : Par),
    PtH X K Cr → LinkG_at X K C bo → ParTie P L K C bo Cr → 0 ≤ bo → 0 ≤ L.LaG → L.sc.p0 D.R.k ≤ L.sc.X' →
    D.host.TT.Nonempty → ChBadp_at X → ChW_at X K →
    PrimeClassLossHypotheses P (PsAt L) (sAt L K) (largeOrderResiduePrimes L) (SizeData₂.lifts D) (TTv D) (badAt X)
      (fun p => G.Sig X K (G.aL L) (G.bL L) p) (fun (_ : Unit) p => G.ioP X K (G.aL L) (G.bL L) p)
      (fun _ => ldAt X K C bo)

def ThickDensitySizeWindowsForAllFamilies : Prop :=
  ∀ (eps : ℝ) (Fm : FamP eps), ChosenTT Fm → ChosenBadp Fm → LinkG Fm → Lnk.LossesSmallShares Fm

def StLoss7W : Prop :=
  ∀ (eps : ℝ) (Fm : FamP eps), ChosenTT Fm → ChosenBadp Fm → ChosenW Fm → LinkG Fm → Lnk.LossF Fm 0

def SmallShareWeightExists : Prop :=
  ∀ (eps : ℝ) (Fm : FamP eps), LinkG Fm → ChosenW Fm

def StOld7 : Prop :=
  ∀ (eps : ℝ) (Fm : FamP eps) (C0 CH : ℝ), ChosenE Fm C0 CH → LinkG Fm → Fm.CoverAll → WeightVectorSmallSharesSeven Fm C0 CH

end Formalism.L2.GlobalTheoryTheory.Loss7

end
