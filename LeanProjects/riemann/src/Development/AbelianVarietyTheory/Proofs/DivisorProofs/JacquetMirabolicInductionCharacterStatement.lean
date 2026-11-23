import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetMirabolicInductionCharacter
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_mirabolic_induction_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.GeometricLemmaFiltration → ∀ {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : Fin 1 ⊕ m ≃ n) {Y : Type} [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (GL m k) Y),
    IsSmooth τ → ∀ (ξ : kˣ →* ℂˣ), IsSmoothChar ξ → ∀ (ϖ : kˣ),
    (∀ (m' : Type) [Fintype m'] [DecidableEq m'] (e' : Fin 1 ⊕ m' ≃ m), ∃ q : Polynomial ℂ,
      q.eval (ξ ϖ : ℂ) ≠ 0 ∧ Polynomial.aeval (jac₂ e' τ (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) q = 0) →
    ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation (jac₂ e (ind₂ e (extTensor (detRep (Fin 1) ξ) τ)))),
      Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧ ∃ t₀ : Fin N,
        Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv (extTensor (detRep (Fin 1) ξ) τ)) ∧
        ∀ t, t ≠ t₀ → ∃ q : Polynomial ℂ, q.eval (ξ ϖ : ℂ) ≠ 0 ∧ ∀ w ∈ (S t.succ).toSubmodule,
          Polynomial.aeval (jac₂ e (ind₂ e (extTensor (detRep (Fin 1) ξ) τ))
            (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) q w ∈ (S t.castSucc).toSubmodule := by
  first | exact @GlobalTheory.JacLineFiltration.jacquet_line_filtration | exact GlobalTheory.JacLineFiltration.jacquet_line_filtration | (intros; apply GlobalTheory.JacLineFiltration.jacquet_line_filtration <;> assumption)
