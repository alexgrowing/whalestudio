import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPolarisedTopChernCoeff

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma continuousAt_dbar_ofReal_of_contDiffAt_one {n : ℕ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hρ : ContDiffAt ℝ 1 ρ v) (w : _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    ContinuousAt (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x w) v := by
  have h : ContDiffAt ℝ 1 (fun y => (ρ y : ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt.comp v hρ
  have hf : ContinuousAt (fderiv ℝ (fun y => (ρ y : ℂ))) v :=
    (h.fderiv_right (m := 0) (by norm_num)).continuousAt
  simp only [_root_.GlobalTheory.dbar_apply]
  fun_prop

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in

theorem _root_.GlobalTheory.GoodTop.continuousAt_corrC :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ}
      {G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n},
      ContDiffAt ℝ 1 ρ v → _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₀ v → IsUnit (G₀ v).det →
        _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₁ v → IsUnit (G₁ v).det →
        ContinuousAt (_root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁) v := by
  intro n r _ _ ρ G₀ G₁ v hρ h₀ hd₀ h₁ hd₁
  have hcurv : ∀ {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G v → IsUnit (G v).det →
      ∀ a b p q, ContinuousAt (fun x => _root_.GlobalTheory.HermFrame.curv G x (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) p q) v :=
    fun hG hdG a b p q =>
      (hG.curv (j := 0) hdG (by norm_num)
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) p q).continuousAt
  have hconn : ∀ {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G v → IsUnit (G v).det →
      ∀ a p q, ContinuousAt
        (fun x => _root_.GlobalTheory.HermFrame.conn G x (_root_.GlobalTheory.GoodMetric.coordVec a) p q) v :=
    fun hG hdG a p q =>
      (hG.conn (j := 0) hdG (by norm_num)
        (_root_.GlobalTheory.GoodMetric.coordVec a) p q).continuousAt
  have hposition : ∀ j : Fin n, ContinuousAt (fun x => _root_.GlobalTheory.GoodTop.mixTop
      (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ x)
        (_root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ x) (_root_.GlobalTheory.GoodTop.curvAt G₀ x) j)) v := by
    intro j
    apply _root_.GlobalTheory.GoodTop.continuousAt_mixTop
    intro i a b p q
    unfold _root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one _root_.GlobalTheory.GoodTop.curvAt _root_.GlobalTheory.GoodTop.cutForm
    split_ifs
    · exact hcurv h₁ hd₁ a b p q
    · exact (continuousAt_dbar_ofReal_of_contDiffAt_one hρ _).mul ((hconn h₁ hd₁ a p q).sub (hconn h₀ hd₀ a p q))
    · exact hcurv h₀ hd₀ a b p q
  have heq : _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ = fun x => ∑ j, _root_.GlobalTheory.GoodTop.mixTop
      (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ x)
        (_root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ x) (_root_.GlobalTheory.GoodTop.curvAt G₀ x) j) := by
    funext x
    rfl
  rw [heq]
  exact tendsto_finset_sum _ fun j _ => hposition j

end GlobalTheory.GoodTop
