import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLeibnizOfCommuteStatement

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.HolAtlas

theorem del_dbar_even_mul (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (w : A.Pt → Ev n) (β : A.Fld)
    (hw : A.IsForm (GlobalTheory.LineForm.fld A w)) (hβ : A.IsForm β) :
    A.del (GlobalTheory.LineForm.fld A w * β) = A.del (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.del β ∧
    A.dbar (GlobalTheory.LineForm.fld A w * β) = A.dbar (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.dbar β := by
  have hloc : ∀ i, A.loc (GlobalTheory.LineForm.fld A w * β) i =
      fun v => A.loc (GlobalTheory.LineForm.fld A w) i v * A.loc β i v := by
    intro i
    funext v
    unfold HolAtlas.loc
    split_ifs
    · rfl
    · simp
  have hd : ∀ α : A.Fld, A.IsForm α → ∀ (x : A.Pt) (S),
      DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd := fun α hα x S =>
    ((hα.smooth x.1.1 S).contDiffAt ((A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)
  have key := fun x : A.Pt => GlobalTheory.T.delOperatorAt_dbarOperatorAt_leibniz_of_commute n (A.loc (GlobalTheory.LineForm.fld A w) x.1.1) (A.loc β x.1.1) x.crd
    (GlobalTheory.LineForm.fld A w x) (hd _ hw x) (hd _ hβ x)
  have hc : ∀ (x : A.Pt) (b : Alt n), b * A.loc (GlobalTheory.LineForm.fld A w) x.1.1 x.crd = GlobalTheory.LineForm.fld A w x * b := by
    intro x b
    rw [A.loc_crd]
    exact Subalgebra.mem_center_iff.1 (w x).2 b
  constructor
  · funext x
    have := (key x).1 fun a => hc x _
    rw [A.loc_crd β x] at this
    simp only [HolAtlas.del, Pi.add_apply, Pi.mul_apply, hloc]
    exact this
  · funext x
    have := (key x).2 fun a => hc x _
    rw [A.loc_crd β x] at this
    simp only [HolAtlas.dbar, Pi.add_apply, Pi.mul_apply, hloc]
    exact this

end GlobalTheory.CxForm.HolAtlas
