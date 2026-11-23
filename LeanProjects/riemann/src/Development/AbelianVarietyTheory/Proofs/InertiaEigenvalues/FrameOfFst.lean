import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DblApply
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLagTerms

variable {D : D7}

def blk (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Matrix (Fin W.rank ⊕ Fin W.rank) (Fin W.rank ⊕ Fin W.rank) D.host.E :=
  g.submatrix finSumFinEquiv finSumFinEquiv

def hAdj (W : HSp D) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  (HSpace.gram W)⁻¹ * (M.map star)ᵀ * HSpace.gram W

def frameOf (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  (hAdj W ((blk W g).toBlocks₂₂ - (blk W g).toBlocks₁₂), hAdj W ((blk W g).toBlocks₁₁ - (blk W g).toBlocks₂₁))

theorem frameOf_fst (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    (frameOf W g).1 = hAdj W ((blk W g).toBlocks₂₂ - (blk W g).toBlocks₁₂) := rfl

theorem frameOf_snd (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    (frameOf W g).2 = hAdj W ((blk W g).toBlocks₁₁ - (blk W g).toBlocks₂₁) := rfl

end GlobalTheory.SWLagTerms

end
