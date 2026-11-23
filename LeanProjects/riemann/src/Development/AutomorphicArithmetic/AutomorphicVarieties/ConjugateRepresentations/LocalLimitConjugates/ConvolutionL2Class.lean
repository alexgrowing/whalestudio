import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.convolution_L2_class :
    UpperTheory.V.Cj.H.ConvolutionL2Class := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ ψ hψ hψs F
  set f : G → ℂ := fun y => ψ y⁻¹ with hfdef
  have hfi : Integrable f μ :=
    (hψ.comp continuous_inv).integrable_of_hasCompactSupport
      (hψs.comp_homeomorph (Homeomorph.inv G))
  have hconv : cv ψ F = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F) := by
    funext x
    show ∫ y, GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x) ∂μ = ∫ y, f y * GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) (x * y) ∂μ
    rw [← MeasureTheory.integral_mul_left_eq_self
      (fun y => GlobalTheory.AutomorphicL2Unitary.lift Γ (↑↑F) y * ψ (y⁻¹ * x)) x]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hfdef, _root_.mul_inv_rev, inv_mul_cancel_right]
    exact mul_comm _ _
  obtain ⟨-, hae⟩ := GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR G Γ μ f hfi F
  rw [hconv]
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv Γ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F)) :=
    (GlobalTheory.AutomorphicL2Unitary.leftInv_lift _).convR f
  have hdesc : GlobalTheory.AutomorphicL2Unitary.descend Γ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F))
      =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ] ↑↑(GlobalTheory.AutomorphicL2Unitary.Rop Γ μ f F) := by
    refine GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.2 ?_
    filter_upwards [hae] with g hg
    have hl := congrFun hinv.lift_descend g
    simp only [GlobalTheory.AutomorphicL2Unitary.lift] at hg hl
    rw [hl, hg]
  have hm : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient Γ μ (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift Γ ↑↑F)) :=
    ⟨hinv, (MeasureTheory.Lp.memLp _).ae_eq hdesc.symm⟩
  exact ⟨hm, GlobalTheory.AutomorphicL2Unitary.l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (hm.lift_toL2_ae_eq.trans hae.symm)⟩
