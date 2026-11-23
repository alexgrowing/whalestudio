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

namespace GlobalTheory.BiJoinDeriv

open GlobalTheory.BiTransfer GlobalTheory.WeilVacMove GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem dLine_apply' {S T : HSp D} {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a))
    {L : ℝ →+ WO S T} (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dLine ψ S T L f w = phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := by
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth
  have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
      f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
    funext t
    rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
  unfold dLine
  rw [e]
  exact (hasDerivAt_exp_mul _ _ f hfs _ w).deriv

theorem dLine_add_line (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {L L' : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (hL' : Continuous L') (hL0' : ∀ t, (L' t).map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T (L + L') f = dLine ψ S T L f + dLine ψ S T L' f := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hS : Continuous (L + L') := hL.add hL'
  have hS0 : ∀ t, ((L + L') t).map (finPart D) = 0 := fun t => by
    rw [AddMonoidHom.add_apply, Matrix.map_add _ (finPart D).map_add, hL0 t, hL0' t, add_zero]
  funext w
  rw [Pi.add_apply, dLine_apply' h hl hlam hS hS0 hf, dLine_apply' h hl hlam hL hL0 hf, dLine_apply' h hl hlam hL' hL0' hf,
    AddMonoidHom.add_apply, map_add, ContinuousLinearMap.map_add]
  have e : phase lam S T (L 1 + L' 1) w = phase lam S T (L 1) w + phase lam S T (L' 1) w := by
    show lam (symplOH S T w (L 1 + L' 1)) = lam (symplOH S T w (L 1)) + lam (symplOH S T w (L' 1))
    rw [symplOH_add_right, map_add]
  rw [e]
  ring

variable {W A A' : HSp D} (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (S : HSp D)

theorem inl_fst_add_inr_snd (x : WO W S) : inlH d S (fstH d S x) + inrH d S (sndH d S x) = x := by
  rw [inlH_apply, inrH_apply, fstH_apply, sndH_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S A' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger A' S (d.resS S x).2) = (d.resS S x).2 :=
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger A' S _
  rw [this, Prod.mk.eta, AddEquiv.symm_apply_apply]

theorem dLine_inlH (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO A S) :
    dLine ψ W S ((inlH d S).comp M) (join d S G) = join d S (fun u v => dLine ψ A S M (fun u' => G u' v) u) := by
  funext x
  simp only [dLine, join_apply]
  congr 1
  funext t
  simp only [heisO, AddMonoidHom.comp_apply, symplOH_split d, map_add, fst_inl, snd_inl,
    GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, join_apply]

theorem dLine_inrH (G : WO A S → WO S A' → ℂ) (M : ℝ →+ WO S A') :
    dLine ψ W S ((inrH d S).comp M) (join d S G) = join d S (fun u v => dLine ψ S A' M (G u) v) := by
  funext x
  simp only [dLine, join_apply]
  congr 1
  funext t
  simp only [heisO, AddMonoidHom.comp_apply, symplOH_split d, map_add, fst_inr, snd_inr,
    GlobalTheory.WeilVacMove.symplOH_zero_right, zero_add, add_zero, join_apply]

end GlobalTheory.BiJoinDeriv

namespace GlobalTheory.BiJoinDeriv

open GlobalTheory.BiTransfer GlobalTheory.WeilVacMove

theorem dLine_join : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W A S A' : HSp D) (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → ∀ M : ℝ →+ WO W S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (∀ s, (GlobalTheory.BiTransfer.fstH d S (M s)).map (finPart D) = 0) ∧ (∀ s, (GlobalTheory.BiTransfer.sndH d S (M s)).map (finPart D) = 0) ∧ GlobalTheory.WeilVacMove.dLine ψ W S M (GlobalTheory.BiTransfer.join d S G) = GlobalTheory.BiTransfer.join d S fun u v => GlobalTheory.WeilVacMove.dLine ψ A S ((GlobalTheory.BiTransfer.fstH d S).comp M) (fun u' => G u' v) u + GlobalTheory.WeilVacMove.dLine ψ S A' ((GlobalTheory.BiTransfer.sndH d S).comp M) (G u) v := by
  intro D ψ hψ W A S A' d G hG M hM hM0
  have h1 : ∀ s, (fstH d S (M s)).map (finPart D) = 0 := fun s => map_mul_eq_zero_left _ (hM0 s) _
  have h2 : ∀ s, (sndH d S (M s)).map (finPart D) = 0 := fun s => fin_dagger A' S (map_mul_eq_zero_left _ (hM0 s) _)
  refine ⟨h1, h2, ?_⟩
  have hj := isThetaFunO_join d hG
  have eM : M = (inlH d S).comp ((fstH d S).comp M) + (inrH d S).comp ((sndH d S).comp M) := by
    ext1 t
    exact (inl_fst_add_inr_snd d S (M t)).symm
  rw [eM, dLine_add_line hψ ((continuous_inlH d S).comp ((continuous_fstH d S).comp hM)) (fun t => map_inlH d S _ (h1 t))
    ((continuous_inrH d S).comp ((continuous_sndH d S).comp hM)) (fun t => fin_inrH d S (h2 t)) hj,
    dLine_inlH, dLine_inrH, ← eM]
  funext x
  simp only [Pi.add_apply, join_apply]

end GlobalTheory.BiJoinDeriv

end
