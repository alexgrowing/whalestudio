import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixesLatticeVacuumPeriodLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceBrk

theorem exp_trace_eq_brk : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ M Y : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M Y) : ℚ) : ℂ)) = brk (HV sc) (embH (tauE D) δ (Matrix.toLin' Y)) (embH (tauE D) δ (Matrix.toLin' M)) := by
  intro D ψ θ S T δ sc h M Y
  have hz : ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) τ i j,
      embH (tauE D) δ (Matrix.toLin' γ) τ i j = δ * tauE D τ (γ i j) := by
    intro γ τ i j
    simp [embH, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  have hδ : δ * starRingEnd ℂ δ = ((‖δ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hHV : HV sc (embH (tauE D) δ (Matrix.toLin' M)) (embH (tauE D) δ (Matrix.toLin' Y)) =
      ((sc * ‖δ‖ ^ 2 : ℝ) : ℂ) * ∑ τ, tauE D τ (GlobalTheory.LatVac.hRat S T M Y) := by
    rw [GlobalTheory.LatSign.hRat_one S T h.gS h.gT]
    simp only [HV, LinearMap.mk₂'ₛₗ_apply, hz, map_sum, map_mul, GlobalTheory.LatSign.tauE_star']
    rw [Complex.ofReal_mul, ← hδ, mul_assoc]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [brk, Formalism.L2.Th1.H.altE, hHV, h.scale, ← GlobalTheory.LatSign.sum_two_re_eq_trace, Complex.im_ofReal_mul,
    Complex.im_sum, ← Complex.ofReal_sum]
  have hs : ∑ τ, 2 * (tauE D τ (D.host.xi0 * GlobalTheory.LatVac.hRat S T M Y)).re =
      -(2 * (Real.sqrt D.host.d)⁻¹ * ∑ τ, (tauE D τ (GlobalTheory.LatVac.hRat S T M Y)).im) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, h.xi, mul_assoc, Complex.I_mul_re, Complex.im_ofReal_mul]
    ring
  rw [hs, Complex.ofReal_neg]
  congr 1
  ring

end GlobalTheory.TraceBrk
