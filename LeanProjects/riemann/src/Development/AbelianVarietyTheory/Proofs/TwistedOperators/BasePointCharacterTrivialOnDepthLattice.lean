import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulMemComplId
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicTraceCharDifferentGenConjIdealCompletionAlStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDiagonalCoordinatesMemComplementIdealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedDiagonalCoordinateMemCompletionConjAAStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdealMembershipCriterionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF

variable {D : D7}

theorem sympl_xZero {V V₀ W W₀ : HSp D} {ρ : ℕ} (dB : HypDec V V₀ ρ) (dJ : HypDec W W₀ ρ) (u : Mx D W.rank V.rank) :
    symplO V W (dB.extX W dJ.jX) (dB.extY W (u ⬝ dB.jY)) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * cA D ((dJ.pY ⬝ u ⬝ dB.jY).trace)) := by
  have h := dB.hO_ext W dJ.jX 0 0 (u ⬝ dB.jY) 0 0
  simp only [map_zero, add_zero, zero_add] at h
  rw [symplO, h]
  congr 2
  have e1 : gA W ⬝ dJ.jX = adj dJ.pY := by rw [dJ.pY_eq, adj_mul, adj_gA, adj_adj]
  simp only [pairS, hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, trace_zero, add_zero, e1]
  rw [← adj_mul, Matrix.mul_assoc]
  exact trace_adj _

end GlobalTheory.XCharBF

theorem GlobalTheory.AscFin.pcBF_xZero_char : OnStd fun {D} _ _ {sc} {G} W F =>
    ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1),
      W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))
        ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h)))
        ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  rw [show xZero (F.dJ ρ h) = (F.dJ ρ h).jX from rfl, GlobalTheory.XCharBF.sympl_xZero]
  refine GlobalTheory.T.psiE_xi0_mul_cA_eq_one_of_mem_complId W.ψ_std _ ?_
  rw [Matrix.trace]
  refine sum_mem fun p _ => ?_
  refine GlobalTheory.T.complementary_ideal_membership_criterion hq μ0 hL G _ (GlobalTheory.T.besselStep_diagonalCoordinates_mem_complementIdeal hF ρ h u hu.1 p) fun e he => ?_
  have := GlobalTheory.T.completed_diagonal_coordinate_mem_completion_conj_AA hF ρ h (e • u) (hu.2 e he) p
  rwa [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at this

end
