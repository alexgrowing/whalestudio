import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairAlongChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_pair_along_chain : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ ∧ I.A.AA = ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) ∧ (∀ τ, B.fields.embC I.A.σ₀ τ = tauE (I.rec7 l Z) τ) ∧ ∀ j, j ≤ B.R.m → ∀ g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j), ∃ x, IsDetRoot _ g x := by
  first | exact @GlobalTheory.AdForm.StdSteps.stdPair_steps | exact GlobalTheory.AdForm.StdSteps.stdPair_steps | (intros; apply GlobalTheory.AdForm.StdSteps.stdPair_steps <;> assumption)
