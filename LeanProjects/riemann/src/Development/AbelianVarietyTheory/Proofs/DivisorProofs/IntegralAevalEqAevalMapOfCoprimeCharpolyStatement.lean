import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAevalEqAevalMapOfCoprimeCharpoly
import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_aeval_eq_aeval_map_of_coprime_charpoly : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ p : K[X], IsIntegral O (aeval γ p) → ∃ r : O[X], aeval γ p = aeval γ (r.map (algebraMap O K)) := by
  first | exact @GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map | exact GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map | (intros; apply GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map <;> assumption)
