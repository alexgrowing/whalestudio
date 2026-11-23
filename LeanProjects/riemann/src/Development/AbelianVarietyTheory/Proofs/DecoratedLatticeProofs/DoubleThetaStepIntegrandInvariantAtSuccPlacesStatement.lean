import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepIntegrandInvariantAtSuccPlaces
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
theorem _root_.GlobalTheory.T.doubleThetaStep_integrand_invariant_at_succ_places : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → (∀ x y, ∀ r ∈ ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ))).prod (R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1)), ∀ κ ∈ (levB fun i => Q i.succ).prod (Q 0).L₂.J, pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x (r * y * κ) = pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y) ∧ (∀ x y, ∀ κ ∈ (levJ fun i => Q i.succ).prod (Q 0).L₁.J, pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x * κ) y = pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y) ∧ (∀ x y, ∀ r ∈ ((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ))).prod (RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1)), pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (r * x) y = pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y) := by
  first | exact @GlobalTheory.QVal.Inv.pint_invariant | exact GlobalTheory.QVal.Inv.pint_invariant | (intros; apply GlobalTheory.QVal.Inv.pint_invariant <;> assumption)
