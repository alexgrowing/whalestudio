import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinSchreierSystemIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_schreier_system_integral : ∀ (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S] [ValuationRing S] [Field K] [Algebra S K] [IsFractionRing S K] (d : ℕ) (U : Matrix (Fin d) (Fin d) S) (z : Fin d → S) (y : Fin d → K), (∀ i, y i ^ p = (U.map (algebraMap S K) *ᵥ y) i + algebraMap S K (z i)) → ∀ i, y i ∈ (algebraMap S K).range := by
  first | exact @GlobalTheory.frobenius_affine_integral | exact GlobalTheory.frobenius_affine_integral | (intros; apply GlobalTheory.frobenius_affine_integral <;> assumption)
