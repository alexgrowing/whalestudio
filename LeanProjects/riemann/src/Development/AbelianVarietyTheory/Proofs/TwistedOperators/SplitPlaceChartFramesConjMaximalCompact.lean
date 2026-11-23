import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

noncomputable section
namespace GlobalTheory.SplitChartLink

theorem block_frame_conjugation_identity {G H : Type} [Group G] [Group H] (f : G →* H) (a x : G) :
    (f a)⁻¹ * f (a * x * a⁻¹) * f a = 1⁻¹ * f x * 1 := by
  simp only [map_mul, map_inv]
  group

theorem rdA_matHom_embV {D : D7} (T : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v) (g : Gv T v) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) (Formalism.L2.Theta.matHom T (embV T v g)) =
      splitHom D.sp.cm.sig T.gram (GlobalTheory.SplitProjChart.emb φ) g := by
  have h1 : GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram g =
      Formalism.UG.bc (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom T (embV T v g)) := by
    have h2 := GlobalTheory.AdelicU.matHom_proj D.sp.cm.sig T.gram v (embV T v g)
    rw [GlobalTheory.AdelicU.proj_emb_self] at h2
    exact h2
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [splitHom_val, h1, GlobalTheory.SplitProjChart.splitProj_emb]
  rfl

theorem link : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∃ φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsIdemOf φ ε ∧ (∃ BS, GlobalTheory.SplitHecke.Frame S ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BS) ∧ ∃ BT, GlobalTheory.SplitHecke.Frame T ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) BT ∧ ∃ ψ : Fv D.host.F v ≃+* w.adicCompletion D.host.E, (∀ a, Valued.v (ψ a) = Valued.v a) ∧ qV D.host.F v = qV D.host.E w ∧ ∃ κ ∈ KGL v T.rank, ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo φ T BT (embV T v (e.symm x)) = κ⁻¹ * Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v) x * κ := by
  intro D S T v w h hv e he ε hε
  obtain ⟨v', φ, hφ, hP⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 ε w hε
  have hv' : v' = v := by
    have := ((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v' φ w hP).1
    subst h
    exact HeightOneSpectrum.ext this.symm
  subst hv'
  have hE : IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  set τ := GlobalTheory.SplitProjChart.emb φ with hτdef
  have hφτ : splitProj τ = φ := GlobalTheory.SplitProjChart.splitProj_emb φ
  have hτ : splitPrime τ = w := ((GlobalTheory.SplitIdemDict.isProjAt_iff τ w).1 (hφτ ▸ hP)).symm
  obtain ⟨hch, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v' φ ε hφ
  have hemb : chartEmb hch = τ := AlgHom.ext fun x => by
    rw [chartEmb_apply, GlobalTheory.SplitProjChart.rdA_incA]; rfl
  have hfr : ∀ (V : HSp D) β, GlobalTheory.SplitHecke.Frame V ε (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) β ↔ IsSplitBasis τ (frameLat V) β :=
    fun V β => by rw [GlobalTheory.AdelicU.SplitFrame.frame_iff_isSplitBasis hφ.1 hch, hemb]
  set ψ := ConjPlace.complEquiv hE h hτ with hψ
  obtain ⟨⟨a, ha, hea⟩, -⟩ := he
  have hBT : IsSplitBasis τ (frameLat T) (Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') a) := by
    rw [← ConjPlace.isFrameAt_iff hE h hτ]
    convert ha
    exact Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have := GlobalTheory.AdelicU.SelfDual.isLattice_frameLat S
  obtain ⟨BS, hBS⟩ := exists_isSplitBasis τ (frameLat S) hE
  refine ⟨φ, hφ, ⟨BS, (hfr S BS).2 hBS⟩, _, (hfr T _).2 hBT, ψ, ConjPlace.valued_complMap hE h hτ, ?_, 1, one_mem _, ?_⟩
  · rw [← hτ, GlobalTheory.LFun.SplitTie.qV_splitPrime]
  · intro x
    have h3 := hea (e.symm x)
    rw [MulEquiv.apply_symm_apply, ConjPlace.locMat_eq hE h hτ, ← hψ] at h3
    have h4 : splitHom D.sp.cm.sig T.gram τ (e.symm x) =
        Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') (a * x * a⁻¹) := by
      have h5 : Formalism.UG.bc (ψ : Fv D.host.F v' →+* w.adicCompletion D.host.E) (splitHom D.sp.cm.sig T.gram τ (e.symm x)) =
          a * x * a⁻¹ := by
        generalize Formalism.UG.bc (ψ : Fv D.host.F v' →+* w.adicCompletion D.host.E) (splitHom D.sp.cm.sig T.gram τ (e.symm x)) = y at h3 ⊢
        subst h3
        group
      rw [← h5]
      exact Units.ext (Matrix.ext fun i j => (ψ.symm_apply_apply _).symm)
    have h6 : Formalism.UG.bc (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') x =
        Matrix.GeneralLinearGroup.map (ψ.symm : w.adicCompletion D.host.E →+* Fv D.host.F v') x := rfl
    rw [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.grpCo, rdA_matHom_embV,
      show splitHom D.sp.cm.sig T.gram (GlobalTheory.SplitProjChart.emb φ) (e.symm x) = _ from h4, ← h6]
    exact block_frame_conjugation_identity _ a x

end GlobalTheory.SplitChartLink
end
