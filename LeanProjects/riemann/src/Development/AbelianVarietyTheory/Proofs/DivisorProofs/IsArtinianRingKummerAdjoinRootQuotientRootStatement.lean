import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingKummerAdjoinRootQuotientRoot
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArtinianRing_kummerAdjoinRoot_quotient_root : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A) (u : Aˣ) (m k : ℕ), Irreducible ϖ → IsUnit (m : A) → 0 < k → IsArtinianRing (AdjoinRoot (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A))) ⧸ Ideal.span {AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)))}) := by
  first | (exact @GlobalTheory.artinian_quot_root_adjoin_kummer) | (exact GlobalTheory.artinian_quot_root_adjoin_kummer) | (intros; apply GlobalTheory.artinian_quot_root_adjoin_kummer  <;> assumption)
