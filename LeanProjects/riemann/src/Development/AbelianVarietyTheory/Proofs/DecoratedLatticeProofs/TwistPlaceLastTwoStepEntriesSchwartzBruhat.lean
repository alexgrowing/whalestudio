import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HatMemSBAndHatOmCol
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QPl.LastTwo

theorem entries_mem_SB : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ) α yb, Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb ∈ SB _ ∧ Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb ∈ SB _ := by
  intro D c v χ Q α yb
  have hreg := Q.reg
  constructor
  · haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.X (Q.s + 1)) (n' := Q.X Q.s)
    refine GlobalTheory.FinPl.Comm.comp_mem_SB (om_mem_SB (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (hreg.1 Q.s 0 rfl))
      (p := fun x₀ => withCol x₀ (Quotient.out yb)) (s := fun x => x.toBlocks₁₁) ?_ ?_ fun x => rfl
    · unfold withCol; fun_prop
    · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))
  · haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.Z ⊕ Unit) (n' := Q.X (Q.s + 1))
    have hv1 : valuation Q.k (-1 : Q.k) = 1 := by simp
    have hh := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol Q.k Q.ψk Q.ν (-1) Q.cond Q.unitVol hv1 (Q.X (Q.s + 1)) 1 1 _
      (cosetInd_mem_SB Q.c₂ yb)).1
    refine GlobalTheory.FinPl.Comm.prod_mem_SB hreg.2.1 hh
      (p := fun x : Matrix (Q.Z ⊕ Unit) (Q.X (Q.s + 1)) Q.k => fromCols x.toRows₁ (0 : Matrix Q.Z (Fin 0) Q.k))
      (r := fun x => x (Sum.inr ()))
      (s := fun z => fromRows z.1.toCols₁ (Matrix.of fun (_ : Unit) => z.2)) ?_ ?_ ?_ ?_
    · exact continuous_pi fun i => continuous_pi fun j => by
        rcases j with j | j
        · exact (continuous_apply j).comp (continuous_apply (Sum.inl i))
        · exact j.elim0
    · exact continuous_apply _
    · exact continuous_pi fun i => continuous_pi fun j => by
        rcases i with i | i
        · exact (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
        · exact (continuous_apply j).comp continuous_snd
    · intro x; ext (i | i) j <;> rfl

end GlobalTheory.QPl.LastTwo
end
