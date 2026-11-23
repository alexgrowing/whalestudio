import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveSplitSupportInvariant
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.move_split_support_invariant : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → A.MoveAt θ i hi c₀ g h → ∀ e, IsSplitIdem (I.rec7 l Z) e → ∀ s s', SuppAt e _ s → SuppAt e _ s' → A.MoveAt θ i hi c₀ (s * g) (s' * h) := by
  first | exact @GlobalTheory.AdForm.SplitMove.moveAt_split | exact GlobalTheory.AdForm.SplitMove.moveAt_split | (intros; apply GlobalTheory.AdForm.SplitMove.moveAt_split <;> assumption)
