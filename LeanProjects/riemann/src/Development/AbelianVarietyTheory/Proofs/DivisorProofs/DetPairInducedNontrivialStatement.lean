import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetPairInducedNontrivial
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_pair_induced_nontrivial : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ), Nontrivial (IndSp (two (stdSum (rfl : u + v = u + v))) ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom)) ∧ HasFiniteLength (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)) := by
  first | exact @GlobalTheory.DetProdNonzero.nontrivial_and_hasFiniteLength | exact GlobalTheory.DetProdNonzero.nontrivial_and_hasFiniteLength | (intros; apply GlobalTheory.DetProdNonzero.nontrivial_and_hasFiniteLength <;> assumption)
