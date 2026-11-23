import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSourceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.TensorTargetRule

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem dagger_resT_symm {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO S A) (v : WO S B) :
    dagger S T ((d.resT S).symm (u, v)) = (d.resS S).symm (dagger S A u, dagger S B v) := by
  rw [d.resT_symm_apply, d.resS_symm_apply, d.pA_eq, d.pB_eq]
  simp only [dagger, adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, cancel₂ (gA_mul_giA A),
    cancel₂ (gA_mul_giA B), Matrix.one_mul]

theorem dagger_resS_symm {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO A S) (v : WO B S) :
    dagger T S ((d.resS S).symm (u, v)) = (d.resT S).symm (dagger A S u, dagger B S v) := by
  have h := dagger_resT_symm d S (dagger A S u) (dagger B S v)
  rw [dagger_dagger, dagger_dagger] at h
  rw [← h, dagger_dagger]

theorem resT_dagger {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (y : WO T S) :
    d.resT S (dagger T S y) = (dagger A S (d.resS S y).1, dagger B S (d.resS S y).2) := by
  have h := dagger_resS_symm d S (d.resS S y).1 (d.resS S y).2
  rw [Prod.mk.eta, AddEquiv.symm_apply_apply] at h
  rw [h, AddEquiv.apply_symm_apply]

theorem resS_dagger {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (x : WO S T) :
    d.resS S (dagger S T x) = (dagger S A (d.resT S x).1, dagger S B (d.resT S x).2) := by
  have h := dagger_resT_symm d S (d.resT S x).1 (d.resT S x).2
  rw [Prod.mk.eta, AddEquiv.symm_apply_apply] at h
  rw [h, AddEquiv.apply_symm_apply]

theorem cj_boxT {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (fA : WO S A → ℂ) (fB : WO S B → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (d.boxT S fA fB) = d.boxS S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) fA) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) fB) := by
  funext y
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, OrthDec.boxT, OrthDec.boxS, resT_dagger, map_mul]

theorem conjAdjoint_cj {S T : HSp D} (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

theorem cj_mem_span {X Y : Type} (e : Y → X) {s : Set (X → ℂ)} {s' : Set (Y → ℂ)} (h : ∀ g ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e g ∈ s')
    {g : X → ℂ} (hg : g ∈ Submodule.span ℂ s) : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e g ∈ Submodule.span ℂ s' := by
  induction hg using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h x hx)
  | zero =>
    have e0 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (0 : X → ℂ) = 0 := by funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e0]; exact zero_mem _
  | add x y _ _ hx hy =>
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (x + y) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e x + GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e y := by funext z; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e1]; exact add_mem hx hy
  | smul c x _ hx =>
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e (c • x) = starRingEnd ℂ c • GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj e x := by funext z; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [e1]; exact Submodule.smul_mem _ _ hx

theorem tensorTarget : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (T A B : HSp D) (d : OrthDec T A B) (S : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.TensorTarget ψ d S := by
  intro D ψ hψ T A B d S
  have thd : ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ↔ IsThetaFunO ψ S T f :=
    fun S T => (GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T).2.2.1
  have src := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hψ T A B d S
  have cc : ∀ f : WO S T → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) = f := fun f => cj_cj _ _ (dagger_dagger S T) f
  refine
    { box_theta := fun fA fB hA hB => d.isThetaFunO_boxT hA hB
      box_zero := fun fA fB => d.boxT_zero S fA fB
      heis_box := fun fA fB => ⟨fun u => ?_, fun v => ?_⟩
      slice_theta := fun f hf => ⟨fun v => ?_, fun u => ?_⟩
      dense := fun f hf => ?_
      om_box := ?_
      om_slice := ?_ }
  · rw [d.heisO_boxT, AddEquiv.apply_symm_apply, heisO_zero']
  · rw [d.heisO_boxT, AddEquiv.apply_symm_apply, heisO_zero']
  · have h1 := (src.slice_theta (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf)).1 (dagger S B v)
    rw [← thd S A]
    convert h1 using 1
    funext u
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger]
  · have h1 := (src.slice_theta (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf)).2 (dagger S A u)
    rw [← thd S B]
    convert h1 using 1
    funext v
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger]
  · intro ε hε
    obtain ⟨g, hg, hgε⟩ := src.dense _ ((thd S T f).2 hf) ε hε
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T) g, cj_mem_span _ ?_ hg, fun x => ?_⟩
    · rintro _ ⟨f1, f2, h1, h2, rfl⟩
      refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S A) f1, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S B) f2, (thd A S f1).2 h1, (thd B S f2).2 h2, ?_⟩
      funext x
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, resS_dagger, map_mul]
    · have h := hgε (dagger S T x)
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_dagger] at h ⊢
      rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
      exact h
  · intro χS χA χB omT omA omB hT hA hB g a b fA fB hfA hfB
    have key := src.om_box χA χB χS (conjAdjoint omT) (conjAdjoint omA) (conjAdjoint omB)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS (χA * χB) omT hT) (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S A χS χA omA hA)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S B χS χB omB hB) a b g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) fA) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) fB)
      ((thd S A fA).2 hfA) ((thd S B fB).2 hfB)
    rw [conjAdjoint_cj, conjAdjoint_cj, ← cj_boxT, ← cj_boxT, conjAdjoint_cj] at key
    have := congrArg (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S T)) key
    rwa [cc, cc] at this
  · intro χS χA χB omT omA omB hT hA hB g a b f hf v
    have key := src.om_slice χA χB χS (conjAdjoint omT) (conjAdjoint omA) (conjAdjoint omB)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS (χA * χB) omT hT) (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S A χS χA omA hA)
      (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S B χS χB omB hB) a b g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f) ((thd S T f).2 hf) (dagger S B v)
    have e1 : (fun u'' => conjAdjoint omB (b, g) (fun v'' => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f ((d.resS S).symm (u'', v''))) (dagger S B v)) =
        GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger A S) (fun u' => omB (g, b) (fun v' => f ((d.resT S).symm (u', v'))) v) := by
      funext u''
      have hfun : (fun v'' => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f ((d.resS S).symm (u'', v''))) =
          GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger B S) (fun v' => f ((d.resT S).symm (dagger A S u'', v'))) := by
        funext v''
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm]
      rw [hfun, conjAdjoint_cj]
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_dagger]
    obtain ⟨k1, k2⟩ := key
    rw [e1] at k1 k2
    refine ⟨(thd S A _).1 k1, fun u => ?_⟩
    have h := k2 (dagger S A u)
    rw [conjAdjoint_cj, conjAdjoint_cj] at h
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger] at h
    exact (starRingEnd ℂ).injective h

end GlobalTheory.TensorTargetRule

end
