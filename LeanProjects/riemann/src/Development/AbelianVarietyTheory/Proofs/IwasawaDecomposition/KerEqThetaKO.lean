import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrientedWeilDatumOfAdelicWeilRepTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoordSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.OrientedKer

variable {D : D7}

theorem toTWsmall_zero (S T : HSp D) : toTWsmall S T 0 = 0 := by
  unfold toTWsmall
  rw [Matrix.zero_mul, Matrix.transpose_zero]

theorem ker_eq_thetaKO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (Wf : WeilFun D ψ) (S T : HSp D) (χS χT : IdC D), S.rank < T.rank → admitted T S χT χS → ∀ om, IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ Φ : ThS ψ T S, (f ≠ 0 → Φ ≠ 0) ∧ ∀ g h, Wf.ker T S χT χS Φ h g = thetaKO om g h f := by
  intro D ψ hψ Wf S T χS χT hr ha om H f hf
  have ha' : admitted S T χS χT := ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩
  obtain ⟨omO, H', e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ S T χS χT _ ha' hr (Wf.core.weil S T χS χT ha')
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D S T hr.le

  have hf0 : IsThetaFun ψ S T fun y => f (E.symm y) := by
    refine (h7 ψ _).1 ?_
    simp only [AddEquiv.symm_apply_apply]
    exact hf
  let Φ₀ : ThS ψ S T := ⟨fun y => f (E.symm y), mem_ThS.2 hf0⟩
  have hfΦ : f = fun x => Φ₀.1 (toTWsmall S T x) := by
    funext x
    simp only [Φ₀, ← hE, AddEquiv.symm_apply_apply]

  have hΦt : IsThetaFun ψ T S fun x => Φ₀.1 x.transpose :=
    (GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ S T Φ₀.1).2.2 hr.ne (mem_ThS.1 Φ₀.2)
  let Φ : ThS ψ T S := ⟨fun x => Φ₀.1 x.transpose, mem_ThS.2 hΦt⟩
  refine ⟨Φ, fun h0 hΦ => h0 ?_, fun g h => ?_⟩
  · funext x
    have := congrFun (congrArg Subtype.val hΦ) (E x).transpose
    simp only [Φ, Φ₀, Matrix.transpose_transpose, AddEquiv.symm_apply_apply, Submodule.coe_zero, Pi.zero_apply] at this
    exact this
  · have hs := Wf.om_swap S T χS χT ha' g h Φ₀ Φ (fun x => congrArg Φ₀.1 (Matrix.transpose_transpose x)) 0
    rw [Matrix.transpose_zero] at hs
    have e1 := congrFun (e (g, h) Φ₀) 0
    rw [toTWsmall_zero, ← hfΦ] at e1
    have e2 := GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S T χS χT omO om H' H (g, h) f hf
    unfold WeilFun.ker thetaKO
    rw [hs, ← e2]
    exact e1.symm

end GlobalTheory.Mem.OrientedKer

end
