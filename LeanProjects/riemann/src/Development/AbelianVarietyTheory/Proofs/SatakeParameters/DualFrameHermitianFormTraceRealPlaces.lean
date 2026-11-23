import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem hOK_vecF : ∀ (D : D7) (X : Fields) (s : Seam D X) (L : PeriodPair) (Λ : AddSubgroup ℂ), L.lattice.toAddSubgroup = Λ → Function.Bijective (tauPl D) → ∀ (N N' : ℕ) (A B : Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area Λ)⁻¹) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
  intro D X s L Λ hΛ hbij N N' A B p _ ι
  subst hΛ
  have hA : (0 : ℝ) < Formalism.L2.Th1.F.area L := Formalism.L2.Th1.F.areaPos_thm L
  have hconj : ∀ (τ : D.what₂.Tau) (x : D.host.E),
      TaylorLogMetric.embT D τ (D.host.conj x) = starRingEnd ℂ (TaylorLogMetric.embT D τ x) := fun τ x =>
    D.host.conjE_apply (TaylorLogMetric.embT D τ) x
  have hL : Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area L.lattice.toAddSubgroup)⁻¹)
      (vecF D s A) (vecF D s B) =
      ∑ τ : X.Tau, TaylorLogMetric.embT D (s.iT τ) (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
    rw [GlobalTheory.FourthRootStd.area_eq]
    unfold Formalism.L2.Th1.GD.hOK Formalism.L2.AlgTh.hSc
    show ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) * ∑ i, ∑ j, _ = _
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [map_sum, map_mul, hconj, vecF]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    have h0 : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    push_cast
    field_simp
  rw [hL, map_sum]
  rw [← Equiv.sum_comp s.iT.symm]
  simp only [Equiv.apply_symm_apply]
  rw [← (Equiv.ofBijective _ hbij).sum_comp]
  rfl

end GlobalTheory.DFrame
