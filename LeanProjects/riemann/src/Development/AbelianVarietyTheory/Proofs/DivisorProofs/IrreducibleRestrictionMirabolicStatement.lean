import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleRestrictionMirabolic
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_restriction_mirabolic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : Fin 1 ⊕ m ≃ n) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [Nontrivial V'] (π : Representation ℂ (GL n k) V) (π' : Representation ℂ (GL m k) V') (hπ : IsSmooth π) (hirr : π.IsIrreducible) (hπ' : IsSmooth π') (hfl : HasFiniteLength π') (ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) (ϖ : kˣ) (N : ℕ) (S : Fin (N + 1) → Subrepresentation (jac₂ e π)) (hS : Monotone S) (h0 : S 0 = ⊥) (hN : S (Fin.last N) = ⊤) (t₀ : Fin N) (φ : (subQuot (S t₀.succ) (S t₀.castSucc)).Equiv (extTensor (detRep (Fin 1) ξ) π')) (hother : ∀ t, t ≠ t₀ → ∃ c : ℂ, c ≠ (ξ ϖ : ℂ) ∧ ∀ w ∈ (S t.succ).toSubmodule, jac₂ e π (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) w - c • w ∈ (S t.castSucc).toSubmodule) (hii : ∀ (m' : Type) [Fintype m'] [DecidableEq m'] (e' : Fin 1 ⊕ m' ≃ m), ∃ q : Polynomial ℂ, q.eval (ξ ϖ : ℂ) ≠ 0 ∧ Polynomial.aeval (jac₂ e' π' (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) q = 0), π'.IsIrreducible := by
  first | exact @GlobalTheory.LeftEndJacquet.isIrreducible | exact GlobalTheory.LeftEndJacquet.isIrreducible | (intros; apply GlobalTheory.LeftEndJacquet.isIrreducible <;> assumption)
