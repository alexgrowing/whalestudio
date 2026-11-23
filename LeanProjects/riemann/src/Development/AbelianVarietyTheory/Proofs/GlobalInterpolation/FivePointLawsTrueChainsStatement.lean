import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FivePointLawsTrueChains
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fivePointLaws_trueChains : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∃ Bd : Built.Dat (I.rec7 l Z) u, Bd.ch = tw (I.tw l l0 Z) u a ∧ (∀ i, i ≤ (I.rec7 l Z).R.m → Nonempty (Split (Bd.J.A i) Bd.J.T)) ∧ Bd.Sees ∧ (∀ i, i < (I.rec7 l Z).R.m → ∃ k : Bd.Ker i, Dat.KerEq k ∧ Dat.KerDil k ∧ Dat.KerUK k ∧ Dat.KerBar k ∧ Dat.KerP k) ∧ Bd = dat I l Z u a := by
  first | exact @GlobalTheory.LvT.Built.TrueLaws.laws_true_fam | exact GlobalTheory.LvT.Built.TrueLaws.laws_true_fam | (intros; apply GlobalTheory.LvT.Built.TrueLaws.laws_true_fam <;> assumption)
