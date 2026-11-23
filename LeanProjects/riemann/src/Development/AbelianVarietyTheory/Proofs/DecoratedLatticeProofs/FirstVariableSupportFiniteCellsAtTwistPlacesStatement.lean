import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstVariableSupportFiniteCellsAtTwistPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstVariable_support_finite_cells_at_twist_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ T₁ : Finset (GA D (c.V (j + 1))), (∀ q ∈ T₁, q ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ α, ∀ g ∈ (w.ε j α).support, ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), flatBF (t.sBF j (σ + 1) h) (t.om j (g, x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧ ∃ q ∈ T₁, ∃ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, x = r * q * k := by
  first | exact @GlobalTheory.QFinSupp.main | exact GlobalTheory.QFinSupp.main | (intros; apply GlobalTheory.QFinSupp.main <;> assumption)
