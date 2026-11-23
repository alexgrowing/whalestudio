import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BiDeriv

open GlobalTheory.BiTransfer

variable {D : D7}

theorem dLine_inl (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO A S) :
    GlobalTheory.WeilVacMove.dLine ψ _ S ((inlH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) (join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S G) =
      join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S (fun u v => GlobalTheory.WeilVacMove.dLine ψ A S M (fun u' => G u' v) u) := by
  funext x
  simp only [GlobalTheory.WeilVacMove.dLine, join_apply]
  congr 1
  funext t
  simp only [heisO, AddMonoidHom.comp_apply, symplOH_split (sumDec A (GlobalTheory.ChiGrid.negSp A')), map_add, fst_inl, snd_inl,
    GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, join_apply]

theorem dLine_inr (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO S A') :
    GlobalTheory.WeilVacMove.dLine ψ _ S ((inrH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) (join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S G) =
      join (sumDec A (GlobalTheory.ChiGrid.negSp A')) S (fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M (G u) v) := by
  funext x
  simp only [GlobalTheory.WeilVacMove.dLine, join_apply]
  congr 1
  funext t
  simp only [heisO, AddMonoidHom.comp_apply, symplOH_split (sumDec A (GlobalTheory.ChiGrid.negSp A')), map_add, fst_inr, snd_inr,
    GlobalTheory.WeilVacMove.symplOH_zero_right, zero_add, add_zero, join_apply]

theorem isBiTheta_dLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → (∀ M : ℝ →+ WO A S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → IsBiTheta ψ A S A' fun u v => GlobalTheory.WeilVacMove.dLine ψ A S M (fun u' => G u' v) u) ∧ ∀ M' : ℝ →+ WO S A', Continuous M' → (∀ s, (M' s).map (finPart D) = 0) → IsBiTheta ψ A S A' fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u) v := by
  intro D ψ hψ A S A' G hG
  have hj := isThetaFunO_join (sumDec A (GlobalTheory.ChiGrid.negSp A')) hG
  refine ⟨fun M hM hM0 => ?_, fun M hM hM0 => ?_⟩
  · have h := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ (L := (inlH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) ((continuous_inlH _ S).comp hM)
      (fun t => map_inlH _ S _ (hM0 t)) hj).2
    rw [dLine_inl] at h
    exact isBiTheta_of_join _ h
  · have h := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ (L := (inrH (sumDec A (GlobalTheory.ChiGrid.negSp A')) S).comp M) ((continuous_inrH _ S).comp hM)
      (fun t => fin_inrH _ S (hM0 t)) hj).2
    rw [dLine_inr] at h
    exact isBiTheta_of_join _ h

end GlobalTheory.BiDeriv

end
