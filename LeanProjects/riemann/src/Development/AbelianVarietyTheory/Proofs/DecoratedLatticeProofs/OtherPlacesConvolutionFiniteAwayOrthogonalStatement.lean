import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OtherPlacesConvolutionFiniteAwayOrthogonal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.otherPlacesConvolution_finite_away_orthogonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)) ∧ ∀ x ∈ (Q 0).D₁.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₁)).support, symplO _ _ x y = 0) ∧ (IsFinComb (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ (Q 0).Away (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)) ∧ ∀ x ∈ (Q 0).D₂.support, ∀ y ∈ (aconv (List.ofFn fun i : Fin r => (Q i.succ).D₂)).support, symplO _ _ x y = 0) := by
  first | exact @GlobalTheory.QVal.inner_supp | exact GlobalTheory.QVal.inner_supp | (intros; apply GlobalTheory.QVal.inner_supp <;> assumption)
