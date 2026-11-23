import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToFourierJacobiHandedFamilyContinuousAutomStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApplyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiActionsMatchThroughLinkMapStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.UnfLink

theorem star_psi {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem heisO_at_zero' {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h]

theorem link : ∀ D : D7, LinkLaw D := by
  intro D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ
  refine ⟨GlobalTheory.T.besselToFourierJacobi_handedFamily_continuous_automorphic D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ, fun G' => ?_⟩
  unfold JacLev.perAll JacLev.per fjAll fjSrcKer
  congr 1; funext h; congr 1; funext n
  have hk := GlobalTheory.T.fourierJacobiKernel_eq_weilRepresentation_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ _ _ s.om₀ s.weil₀ Ξ hΞ
  obtain ⟨hp, hc⟩ := GlobalTheory.T.jacobiActions_match_through_linkMap D ρ ρ B L' ζ' hz l J.W J.W₀ J.d n.1 n.2
  simp only [fjAllFun, fjSrcKerFun, JacLev.ker, jacS, handBF, hk, Pi.smul_apply, smul_eq_mul, heisO_at_zero', hp, hc]
  rw [star_mul', star_star, star_psi s.weil₀.std]
  simp_rw [mul_left_comm (φ _) (ψ _)]
  rw [integral_const_mul]
  ring

end GlobalTheory.UnfLink
