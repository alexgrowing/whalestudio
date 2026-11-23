import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFullRankBesselBasePointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselGroupActsBasePointUnitriangularStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.FBL

variable {D : D7} {σ : ℕ}

def zlQ (B : BesL D σ) : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E := vecMulVec B.ζ (GlobalTheory.Unf.FB.eLast D (σ + 1))

theorem rat_zlQ (B : BesL D σ) : (rat (zlQ B) : Mx D B.L.rank (σ + 1)) = zEll B.L (σ + 1) B.ζ := by
  rw [zEll, ← GlobalTheory.Unf.FB.ratV_eLast]
  funext i j
  simp [rat, zlQ, vecMulVec_apply, ratV]

theorem gramQ_zlQ_mulVec_last (B : BesL D σ) (a : Fin (σ + 1) → D.host.E) :
    (gramQ B.L (zlQ B) *ᵥ a) (Fin.last σ) = (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a (Fin.last σ) := by
  simp only [gramQ, zlQ, Matrix.mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply,
    GlobalTheory.Unf.FB.eLast, Pi.star_apply, Fin.val_last]
  simp only [if_true, mul_one, star_one]
  rw [Finset.sum_eq_single (Fin.last σ)]
  · simp only [Fin.val_last, if_true, mul_one]
  · intro b _ hb
    have hb' : ¬ (b.1 + 1 = σ + 1) := fun h => hb (Fin.ext (by simp only [Fin.val_last]; omega))
    simp only [hb', if_false, mul_zero, Finset.sum_const_zero, zero_mul]
  · simp

theorem basePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (xLast B.d (vecB B.o B.ζ)) = d.qS B.L c (zEll B.L (σ + 1) B.ζ) := by
  intro D σ B
  obtain ⟨x, ⟨hli, hg⟩, hx⟩ := GlobalTheory.T.exists_rational_fullRank_besselBasePoint D σ B
  rw [← rat_zlQ] at hg
  have hG : gramQ B.V x = gramQ B.L (zlQ B) := GlobalTheory.Unf.FB.gramQ_eq_of_gramSkew x (zlQ B) hg
  have hA : adj (xLast B.d (vecB B.o B.ζ)) ⬝ (gA B.V ⬝ xLast B.d (vecB B.o B.ζ)) =
      adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) := by
    rw [← hx, ← rat_zlQ, ← GlobalTheory.Unf.FB.rat_gramQ, ← GlobalTheory.Unf.FB.rat_gramQ, hG]
  refine ⟨x, hx, ⟨hli, fun u hu => ?_⟩, ?_, fun a ha => ?_, fun S S₀ d c => ?_⟩
  · rw [GlobalTheory.Unf.FB.rat_gramQ, hx, hA]
    have hz : zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := zEll_mul B.L B.ζ hu
    calc adj u.1 ⬝ (adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) ⬝ u.1)
          = adj (zEll B.L (σ + 1) B.ζ ⬝ u.1) ⬝ (gA B.L ⬝ (zEll B.L (σ + 1) B.ζ ⬝ u.1)) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) := by rw [hz]
  · ext g
    rw [hx]
    exact ((GlobalTheory.T.besselGroup_acts_basePoint_unitriangular D σ B).1 g).symm
  · have h1 := congrFun ha (Fin.last σ)
    rw [hG, gramQ_zlQ_mulVec_last, Pi.zero_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left B.line.2
  · rw [HypDec.qS, HypDec.qS, HypDec.symplOH_extX_extY, HypDec.symplOH_extX_extY, GlobalTheory.Unf.FB.pairS_mul,
      GlobalTheory.Unf.FB.pairS_mul, hA]

end GlobalTheory.Asc.FBL
