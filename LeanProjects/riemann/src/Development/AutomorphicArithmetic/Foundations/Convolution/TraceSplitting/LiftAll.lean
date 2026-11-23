import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftStep

theorem UpperTheory.ConvolutionTheory.T.liftAll :
    UpperTheory.ConvolutionTheory.T.LiftStep → UpperTheory.ConvolutionTheory.T.LiftAll := by
  intro h F E _ _ _ _ _ _ _ _ σ hσ hp n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn π
    induction π using Quotient.inductionOn with
    | _ π =>
      rcases h F E σ hσ hp n hn (fun m h1 h2 => ih m h2 h1) π with ⟨ι, hι, m, Q, hm, hc, hw⟩ | ⟨P, hP, -⟩
      · exact ⟨ι, hι, m, Q, hm, Fintype.card_pos_iff.1 (by omega), hw⟩
      · refine ⟨Unit, inferInstance, fun _ => n, fun _ => GlobalTheory.CuspRep.CG.mk P, fun _ => hn, ⟨()⟩, ?_⟩
        rw [UpperTheory.ConvolutionTheory.R.sumSat_unit]
        exact hP.1
