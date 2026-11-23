import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.KapAdjLine

theorem kap_starAdj : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (x : WO (negSp F.Lz) (G.V (.core (2 * ρ + 1)))), (F.lnk ρ).κ _ (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ x) = x := by
  unfold OnStd
  intro D _ _ _ _ _ _ G _ _ _ F hF ρ x
  have hτ : (F.lnk ρ).τ = D.host.xi0 • (1 : Matrix (Fin (negSp F.Lz).rank) (Fin (negSp F.Lz).rank) D.host.E) := by
    have hl := F.line ρ
    have hu : Unique (Fin (negSp F.Lz).rank) := by rw [hl.1]; infer_instance
    have hz : F.ζ (ρ + 1) = (-D.host.xi0) • F.ζ ρ := by rw [hF.ζ, hF.ζ (ρ), pow_succ', mul_smul]
    have e : (F.lnk ρ).τ *ᵥ F.ζ ρ = -((-D.host.xi0) • F.ζ ρ) := by rw [← hz]; exact (F.lnk ρ).map
    have h2 := hl.2
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at h2
    have b : F.ζ ρ default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
    have e1 := congrFun e default
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_unique, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_mul, neg_neg] at e1
    funext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact mul_right_cancel₀ b e1
  rw [Lnk.κ, hτ, rat_smul, rat_one, Matrix.smul_mul, Matrix.one_mul, smul_smul, ← map_mul,
    mul_inv_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one, one_smul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]

end GlobalTheory.KapAdjLine
