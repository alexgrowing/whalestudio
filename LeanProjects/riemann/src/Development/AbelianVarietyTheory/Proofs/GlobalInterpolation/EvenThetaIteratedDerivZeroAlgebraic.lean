import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.TorsValsFinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JInvNormLeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicIsogenyConstantOfIsogenyFormula

noncomputable section

namespace GlobalTheory.ThetaZeroAlg

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker
open GlobalTheory.IsogConst

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem omegaK_eq (d : ℕ) : Formalism.L2.Th1.CM.omegaK d = Formalism.L2.Th1.F.cmTheta 1 d := by
  unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring

theorem hasCMBy (B : Base D cc δ) : Formalism.L2.Th1.CM.HasCMBy D.host.d B.L := by
  intro ω hω
  rw [omegaK_eq]
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B ω hω

theorem disc_one (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.g₂ ^ 3 - 27 * B.L.g₃ ^ 2 = 1 := by
  have hL' : (B.L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← B.lat]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ B.L hL'
  have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  rw [← e2, ← e3]
  exact h

theorem d_sq (D : D7) : Squarefree D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).squarefree

theorem host_imagQuadratic_discriminant_mod_four (D : D7) : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega

theorem g₂_g₃_mem_Qbar (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.g₂ ∈ TaylorLogMetric.Qbar ∧ B.L.g₃ ∈ TaylorLogMetric.Qbar := by
  have hdisc := disc_one B hcc hδ
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv B.L) := GlobalTheory.ThLoc.cm1 D.host.d B.L (d_sq D) (host_imagQuadratic_discriminant_mod_four D) (hasCMBy B)
  have hjQ : Formalism.L2.Th1.CM.jInv B.L ∈ TaylorLogMetric.Qbar :=
    (qbar_iff _).2 (hj.tower_top (A := ℚ)).isAlgebraic
  have hg2c : B.L.g₂ ^ 3 = Formalism.L2.Th1.CM.jInv B.L / 1728 := by
    unfold Formalism.L2.Th1.CM.jInv; rw [hdisc]; ring
  have h2 : B.L.g₂ ∈ TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 3) (by norm_num) ?_
    rw [hg2c]; exact div_mem hjQ (nat_mem 1728)
  have h3sq : B.L.g₃ ^ 2 = (B.L.g₂ ^ 3 - 1) / 27 := by rw [← hdisc]; ring
  have h3 : B.L.g₃ ∈ TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 2) (by norm_num) ?_
    rw [h3sq]
    exact div_mem (sub_mem (pow_mem h2 3) (one_mem _)) (nat_mem 27)
  exact ⟨h2, h3⟩

theorem kernelBase_periodLattice_sigmaTwo_algebraic (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    Formalism.L2.Th1.F.s2 B.L ∈ TaylorLogMetric.Qbar := by
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  have hd0 : 0 < D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).pos
  obtain ⟨S, -, -, hIso, -⟩ := Formalism.L2.Th1.F.hasCMByIsogeny D.host.d B.L (hasCMBy B) (-1) 2 (by simp) hd0
  have hαsq := alpha_sq D.host.d
  have hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ TaylorLogMetric.Qbar :=
    qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))
  have hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0 := by
    intro h0
    rw [h0] at hαsq
    have : (D.host.d : ℂ) = 0 := by linear_combination hαsq
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have he : InQ (Formalism.L2.Th1.F.pSeries B.L) := by
    intro k
    rw [Formalism.L2.KerInert.AlgP.pSeries_eq_map TaylorLogMetric.Qbar B.L h2 h3, PowerSeries.coeff_map]
    exact SetLike.coe_mem _
  have hc := algebraic_isogenyConstant_of_isogenyFormula _ he _ _ hα hα0 _ hIso
  rw [hαsq] at hc
  have hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) := by
    push_cast; ring
  rw [hN] at hc
  have hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card S + 1 + D.host.d ≠ 0)
  have e : Formalism.L2.Th1.F.s2 B.L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ *
      (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 B.L) := by
    rw [← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rw [e]
  exact mul_mem (inv_mem (natCast_mem _ _)) hc

theorem weierstrassP_halfPeriod_algebraic (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.weierstrassP (B.ω₀ / 2) ∈ TaylorLogMetric.Qbar := by
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  haveI : Algebra.IsAlgebraic ℚ TaylorLogMetric.Qbar :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 x.2)⟩
  have hN : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) ∈ B.L.lattice := by
    have e : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) = B.ω₀ := by push_cast; ring
    rw [e]; exact B.omega_mem
  have hx : IsAlgebraic ℚ (B.L.weierstrassP (B.ω₀ / 2)) :=
    (PI.GalTorsConj.W.wp_isAlgebraic B.L TaylorLogMetric.Qbar h2 h3 2 (B.ω₀ / 2) (by norm_num) hN
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B)).restrictScalars ℚ
  exact mem_algebraicClosure_iff.2 hx

theorem evenTheta_iteratedDeriv_zero_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ k : ℕ, iteratedDeriv k B.th0 0 ∈ TaylorLogMetric.Qbar := by
  intro D cc δ B hcc hδ k
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  have hc := Formalism.L2.KerInert.AlgP.theta_null_coefficients B.L B.ω₀ B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B) TaylorLogMetric.Qbar h2 h3
    (kernelBase_periodLattice_sigmaTwo_algebraic B hcc hδ) (weierstrassP_halfPeriod_algebraic B hcc hδ) k
  unfold Formalism.L2.Th1.F.taylor0 at hc
  rw [PowerSeries.coeff_mk] at hc
  have hf : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have e : iteratedDeriv k B.th0 0 = ((k.factorial : ℕ) : ℂ) *
      (iteratedDeriv k (Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2)) 0 / ((k.factorial : ℕ) : ℂ)) := by
    rw [mul_div_cancel₀ _ hf]; rfl
  rw [e]
  exact mul_mem (natCast_mem _ _) hc

end GlobalTheory.ThetaZeroAlg
