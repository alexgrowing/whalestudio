import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleTwistedCoboundary
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cocycle_twisted_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k : ℕ) (χ κ : Gal p Ω → ZMod (p ^ k)), IsKum T k (Ggeo p Ω) (T.qq k) κ →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω) a → IsTwistedOneCocycle 0 k (Ggeo p Ω) χ a →
      ∃ o : Ω, IsInt p o ∧ (∀ g ∈ Ggeo p Ω, g o = o) ∧
        IsTwistedOneCoboundary 0 k (Ggeo p Ω) χ (fun g => (p : Ω) ^ c * a g - o * ((κ g).val : Ω))) ∧
  (∀ o : Ω, IsInt p o → (∀ g ∈ Ggeo p Ω, g o = o) →
      IsTwistedOneCoboundary 0 k (Ggeo p Ω) χ (fun g => o * ((κ g).val : Ω)) → Cong p k ((p : Ω) ^ c * o) 0) := by
  first | exact @GlobalTheory.K5.TopGeo.top | exact GlobalTheory.K5.TopGeo.top | (intros; apply GlobalTheory.K5.TopGeo.top <;> assumption)
