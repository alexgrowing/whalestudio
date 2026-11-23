import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameOfFst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLagTerms
variable {D : D7}

theorem cA_incA_loc (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem adjO_mul_rat (V W : HSp D) (y : Mx D V.rank W.rank) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    GlobalTheory.PairLift.adjO V W (HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (M.map (incA D))) =
      ratMul (hAdj W M) (GlobalTheory.PairLift.adjO V W y) := by
  have e : ((M.map (incA D)).map (cA D))ᵀ = ((M.map star)ᵀ).map (incA D) := by
    ext i j; simp [cA_incA_loc]
  rw [GlobalTheory.AdjLawPf.adjO_eq, GlobalTheory.AdjLawPf.adjO_eq, GlobalTheory.AdjLawPf.conjT_mul, e]
  unfold ratMul hAdj
  rw [Matrix.map_mul, Matrix.map_mul]
  have g1 : (HSpace.gram W).map (incA D) * (HSpace.gram W)⁻¹.map (incA D) = 1 :=
    mul_eq_one_comm.1 (GlobalTheory.AdjLawPf.inv_mul_gram W)
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((HSpace.gram W).map (incA D)), g1, Matrix.one_mul]

theorem act_lagr (V W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (hg : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) (y : Mx D V.rank W.rank) :
    actO (GlobalTheory.Doubling.dblSp W) V γ⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y) =
      HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D)) := by
  unfold actO
  rw [inv_inv, hg, GlobalTheory.AdjLawPf.mt_one, Matrix.one_mul]

theorem resL_lagr (V W : HSp D) (y : Mx D V.rank W.rank)
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL W V (HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D))) =
      HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (((blk W g₀).toBlocks₁₁ - (blk W g₀).toBlocks₂₁).map (incA D)) := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [GlobalTheory.SiegelFormula.lagr, Matrix.of_apply, GlobalTheory.Doubling.pairVec_inl, GlobalTheory.Doubling.pairVec_inr, blk,
    Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.sub_apply, map_sub, mul_sub,
    Finset.sum_sub_distrib, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  abel

theorem resR_lagr (V W : HSp D) (y : Mx D V.rank W.rank)
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    -GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR W V (HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D))) =
      HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (((blk W g₀).toBlocks₂₂ - (blk W g₀).toBlocks₁₂).map (incA D)) := by
  ext i j
  simp only [Matrix.neg_apply, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [GlobalTheory.SiegelFormula.lagr, Matrix.of_apply, GlobalTheory.Doubling.pairVec_inl, GlobalTheory.Doubling.pairVec_inr, blk,
    Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.sub_apply, map_sub, mul_sub,
    Finset.sum_sub_distrib, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  abel

theorem dbl_actO_lagr : ∀ (D : D7) (V W : HSp D) (f₁ f₂ : WO V W → ℂ) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E),
    Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → ∀ (y : Mx D V.rank W.rank),
    GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V γ⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) =
      f₁ (ratMul (frameOf W g₀).1 (GlobalTheory.PairLift.adjO V W y)) * star (f₂ (ratMul (frameOf W g₀).2 (GlobalTheory.PairLift.adjO V W y))) := by
  intro D V W f₁ f₂ γ g₀ hg y
  rw [act_lagr V W γ g₀ hg y, GlobalTheory.SWPairProof.dbl_apply, resL_lagr, resR_lagr, adjO_mul_rat, adjO_mul_rat,
    frameOf_fst, frameOf_snd, starRingEnd_apply, mul_comm]

end GlobalTheory.SWLagTerms
