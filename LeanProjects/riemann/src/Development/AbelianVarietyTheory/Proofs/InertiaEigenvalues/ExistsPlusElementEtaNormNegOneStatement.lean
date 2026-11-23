import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlusElementEtaNormNegOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_plus_element_eta_norm_neg_one : ∀ (K : UQ) (B : InvAlg K) (f : B.A), IsIdempotentElem f → f ≠ 0 → (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) → B.σ f = f → ∃ y : B.A, B.Plus y ∧ y * (1 - f) = 1 - f ∧ K.eta (Algebra.norm K.E y) = -1 := by
  first | exact @GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one | exact GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one | (intros; apply GlobalTheory.UnitLemma.Desc.exists_plus_eta_norm_neg_one <;> assumption)
