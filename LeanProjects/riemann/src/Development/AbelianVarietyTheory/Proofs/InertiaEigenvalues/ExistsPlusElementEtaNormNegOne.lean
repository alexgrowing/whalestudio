import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardResidueFieldAdjoinUnitaryProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfFinite

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem exists_plus_eta_norm_neg_one : ∀ (K : UQ) (B : InvAlg K) (f : B.A), IsIdempotentElem f → f ≠ 0 →
    (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) → B.σ f = f →
    ∃ y : B.A, B.Plus y ∧ y * (1 - f) = 1 - f ∧ K.eta (Algebra.norm K.E y) = -1 := by
  first
  | exact @_root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm
  | exact _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm
  | (apply _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm ..)

end GlobalTheory.UnitLemma.Desc
