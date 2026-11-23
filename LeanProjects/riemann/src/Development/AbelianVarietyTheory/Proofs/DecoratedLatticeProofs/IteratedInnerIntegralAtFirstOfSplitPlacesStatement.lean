import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedInnerIntegralAtFirstOfSplitPlaces
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
theorem _root_.GlobalTheory.T.iteratedInnerIntegral_at_first_of_splitPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ m₁ s₁ m₂ s₂, LocNorm (Q 0) m₁ s₁ m₂ s₂ → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → ∀ x ∈ grpAt S.J.W (places fun i => Q i.succ), ∀ y ∈ grpAt S.B'.V (places fun i => Q i.succ), Iter2 s₁ m₁ s₂ m₂ (fun x₀ y₀ => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x * (Q 0).gl₁ x₀) (y * (Q 0).gl₂ y₀)) (innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y) := by
  first | exact @GlobalTheory.QValInner.innerVal_iter2 | exact GlobalTheory.QValInner.innerVal_iter2 | (intros; apply GlobalTheory.QValInner.innerVal_iter2 <;> assumption)
