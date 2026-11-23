import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositionSeriesIntertwiningChain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
open scoped TensorProduct
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.composition_series_intertwining_chain : ∀ (L J : Type) [Group L] [AddCommGroup J] [Module ℂ J] (ρ : Representation ℂ L J) (N : ℕ)
    (S : Fin (N + 1) → Subrepresentation ρ), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ →
    ∀ (t₀ : Fin N) (z : Fin N → L) (c : Fin N → ℂ), (∀ t y, y * z t = z t * y) →
      (∀ t, t ≠ t₀ → ∀ y, subQuot (S t.succ) (S t.castSucc) (z t) y = c t • y) →
      ∃ (l : List (Fin N)) (A : Representation.IntertwiningMap (subQuot (S t₀.succ) (S t₀.castSucc)) ρ),
        (∀ t ∈ l, t ≠ t₀) ∧ ∀ w, (l.map fun t => ρ (z t) - c t • (1 : Module.End ℂ J)).prod w ∈ LinearMap.range A.toLinearMap := by
  first | exact @GlobalTheory.FiltStepCut.exists_prod_mem_range | exact GlobalTheory.FiltStepCut.exists_prod_mem_range | (intros; apply GlobalTheory.FiltStepCut.exists_prod_mem_range <;> assumption)
