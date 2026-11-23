import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MxAtOfMemDepLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiUnipotentTrivialOnLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingFourierJacobiStepBasePointColumnStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEOffS0ColumnPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEAtS0ColumnPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB
variable {D : D7}

theorem charx_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)),
    (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' ∈ latRow G (2 * σ + 2) →
      W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (xFB F σ h'))
        ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a')) = 1 := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' a' ha'
  have hh := (F.dJ (σ + 1) h).hO_ext (G.V (.grid (2 * σ + 2) 0)) (xFB F σ h') 0 0 a' 0 0
  simp only [map_zero, zero_add, add_zero] at hh
  rw [symplO, hh, show hO (G.V (.core (2 * (σ + 1) + 1))) (G.V (.grid (2 * σ + 2) 0)) 0 0 = 0 by simp [hO],
    show pairS (G.V (.grid (2 * σ + 2) 0)) (0 : Mx D _ (σ + 1)) 0 = 0 by simp [pairS], add_zero, add_zero,
    pairS_eq_sum, Finset.mul_sum]
  change psiE W.ψ _ = 1
  refine Finset.sum_induction _ (fun z => psiE W.ψ z = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul])
    (psiE_zero W.ψ) fun p _ => ?_
  rw [GlobalTheory.T.hermitianPairing_fourierJacobi_step_basePoint_columns D hD T L μ0 hL sc G W M hM F hF σ h h' a' p]
  refine GlobalTheory.FinPl.PsiUnit.psiE_eq_one_of_local W.ψ W.ψ_std.1.1 (P := fun _ => True) ?_ fun v _ => ?_
  · have hu : MxAt (fun _ => True) ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a') :=
      mxAt_of_mem_depLat (p := .chi (2 * σ + 2) 0) ha'
    refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (GlobalTheory.LastOpPf.cA_mem_idAt ?_))
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hu k l)
  · by_cases hv : v ∈ G.pl.S0
    · exact GlobalTheory.T.psiE_at_S0_column_pair D hD T L μ0 hL sc G W M hM σ h h' _ ha' p v hv
    · exact GlobalTheory.T.psiE_off_S0_column_pair D hD T L μ0 hL sc G W M hM σ h h' _ ha' p v hv

end GlobalTheory.CharXFB
