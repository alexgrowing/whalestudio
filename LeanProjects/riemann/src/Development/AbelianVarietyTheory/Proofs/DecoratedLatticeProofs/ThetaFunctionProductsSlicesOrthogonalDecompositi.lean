import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.BoxSlice

open GlobalTheory.MixModel.OrthDec

variable {D : D7} {S A B : HSp D} (d : GlobalTheory.MixModel.OrthDec S A B)

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp only [heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem resS_symm_left (T : HSp D) (u : WO A T) :
    (d.resS T).symm (u, 0) = GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA u := by
  rw [resS_symm_apply, GlobalTheory.MixModel.sandwich_apply, Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem isThetaFunO_slice_left {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (v : WO B T) : IsThetaFunO ψ A T fun u => f ((d.resS T).symm (u, v)) where
  quasi γ u := by
    have e0 : (d.resS T).symm (ratW T A γ, 0) = ratW T S (γ * d.qA) := by
      rw [resS_symm_apply, Matrix.zero_mul, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    have e : ((ratW T A γ + u, v) : WO A T × WO B T) = (ratW T A γ, (0 : WO B T)) + (u, v) := by simp
    show f ((d.resS T).symm (ratW T A γ + u, v)) = ψ (-(symplOH A T (ratW T A γ) u)) * f ((d.resS T).symm (u, v))
    rw [e, map_add, e0, hf.quasi, ← e0, d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.MixModel.symplOH_zero_left, add_zero]
  level := by
    obtain ⟨U, hU, k⟩ := hf.level
    refine ⟨U.comap (GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA),
      hU.preimage (GlobalTheory.MixModel.continuous_sandwich _ _), fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (k _ hu (GlobalTheory.MixModel.map_sandwich _ _ _ h0)) ((d.resS T).symm (w, v))
    rw [← resS_symm_left] at e1
    simp only [heisO] at e1 ⊢
    rw [← e1, ← map_add (d.resS T).symm, Prod.mk_add_mk, add_zero, d.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  cont := hf.cont.comp ((d.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const))
  smooth k L hL h0 w := by
    have e : ∀ t, (d.resS T).symm (w + L t, v) =
        (d.resS T).symm (w, v) + ((GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA).comp L) t := by
      intro t
      rw [AddMonoidHom.comp_apply, ← resS_symm_left, ← map_add (d.resS T).symm, Prod.mk_add_mk, add_zero]
    simp only [e]
    exact hf.smooth k ((GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA).comp L)
      ((GlobalTheory.MixModel.continuous_sandwich _ _).comp hL) (fun t => GlobalTheory.MixModel.map_sandwich _ _ _ (h0 t)) _

theorem isThetaFunO_slice_right {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (u : WO A T) : IsThetaFunO ψ B T fun v => f ((d.resS T).symm (u, v)) := by
  have h := isThetaFunO_slice_left d.symm hf u
  have e : ∀ v, (d.symm.resS T).symm (v, u) = (d.resS T).symm (u, v) := fun v => by
    rw [resS_symm_apply, resS_symm_apply, add_comm]; rfl
  simp only [e] at h
  exact h

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), (∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (o.boxS T fA fB)) ∧ (∀ fA fB, o.boxS T fA fB 0 = fA 0 * fB 0) ∧ (∀ fA fB, (∀ u, heisO ψ S T ((o.resS T).symm (u, 0)) (o.boxS T fA fB) = o.boxS T (heisO ψ A T u fA) fB) ∧ ∀ v, heisO ψ S T ((o.resS T).symm (0, v)) (o.boxS T fA fB) = o.boxS T fA (heisO ψ B T v fB)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ v, IsThetaFunO ψ A T fun u => f ((o.resS T).symm (u, v))) ∧ ∀ u, IsThetaFunO ψ B T fun v => f ((o.resS T).symm (u, v)) := by
  intro D ψ _ S A B T o
  refine ⟨fun fA fB hA hB => o.isThetaFunO_boxS hA hB, fun fA fB => o.boxS_zero T fA fB,
    fun fA fB => ⟨fun u => ?_, fun v => ?_⟩, fun f hf => ⟨fun v => isThetaFunO_slice_left o hf v,
      fun u => isThetaFunO_slice_right o hf u⟩⟩
  · rw [o.heisO_boxS, AddEquiv.apply_symm_apply, heisO_zero']
  · rw [o.heisO_boxS, AddEquiv.apply_symm_apply, heisO_zero']

end GlobalTheory.BoxSlice

end
