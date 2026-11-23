import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRootPowerSumMapGaloisEq
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_rootPowerSum_map_galois_eq : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (θ : AlgebraicClosure F' →* ℂ) (k : ℕ) (P : F'[X]), ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) = ∏ j ∈ Finset.range (Module.finrank F F'), rootSum θ (k * Nat.card F ^ j) P := by
  first | (exact @GlobalTheory.Shin.prod_rootSum_map_algEquiv) | (exact GlobalTheory.Shin.prod_rootSum_map_algEquiv) | (intros; apply GlobalTheory.Shin.prod_rootSum_map_algEquiv  <;> assumption)
