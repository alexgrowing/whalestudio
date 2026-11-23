import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistChainLevelProduct_inverse_scalar_laws : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ → t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧ t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  first | exact @GlobalTheory.QFinLaw.inverse_laws | exact GlobalTheory.QFinLaw.inverse_laws | (intros; apply GlobalTheory.QFinLaw.inverse_laws <;> assumption)
