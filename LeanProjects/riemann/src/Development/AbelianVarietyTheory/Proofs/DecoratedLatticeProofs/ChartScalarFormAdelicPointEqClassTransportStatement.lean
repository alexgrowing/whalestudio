import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartScalarFormAdelicPointEqClassTransport
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartScalarForm_adelicPoint_eq_classTransport : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b (c : (I.chain l u a).cls j) (d : (I.stp u a j).D c.1)
    (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (z : TC.GA B (B.R.N j)), x ∈ GfC _ →
    z.1 = finM _ (rankN (I.rec7 l Z) j hj) x → TC.PtOf (z * A.kb j b) (extTo I.SQ d.1.1) →
    A.chOf j ((I.stp u a j).cl c.1 d) = b →
    cosetIn d = cosetIn ((I.stp u a j).rep ((I.stp u a j).cl c.1 d)) → ∀ y,
      A.rd θ j hj b φ y x = (I.stp u a j).trTo B.fields.emb B.embLL c.1 d (φ ((I.stp u a j).cl c.1 d)) y := by
  first | exact @GlobalTheory.AdForm.rd_trTo | exact GlobalTheory.AdForm.rd_trTo | (intros; apply GlobalTheory.AdForm.rd_trTo <;> assumption)
