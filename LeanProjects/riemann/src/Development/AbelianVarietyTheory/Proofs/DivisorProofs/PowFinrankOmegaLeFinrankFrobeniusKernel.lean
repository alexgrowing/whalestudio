import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeFrobeniusKernelMulSpanPrimePowersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSpanPowPDivGroupLevelLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDualStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.PDivGroup

theorem pow_finrank_omega_le_finrank_frobKer : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K), ∀ r : ℕ,
    (p ^ r) ^ Module.finrank K G.omega ≤ Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) := by
  intro p _ K _ h G r
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
  have hN : Module.finrank K (G.A r) = p ^ (r * G.height) := by
    have := G.rank_eq r (IsLocalRing.closedPoint K)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hdim := (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G).2.2.2
  have hord := GlobalTheory.T.finrank_le_frobeniusKernel_mul_span_primePowers p K (G.A r) r
  have hspan := GlobalTheory.T.finrank_span_pow_pDivGroup_level_le p K h G r
  have hpos : 0 < (p ^ r) ^ Module.finrank K G.dual.omega :=
    pow_pos (pow_pos (Fact.out : p.Prime).pos _) _
  have key : (p ^ r) ^ Module.finrank K G.omega * (p ^ r) ^ Module.finrank K G.dual.omega ≤
      Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) * (p ^ r) ^ Module.finrank K G.dual.omega := by
    rw [← pow_add, hdim, ← pow_mul, ← hN]
    exact hord.trans (Nat.mul_le_mul_left _ hspan)
  exact Nat.le_of_mul_le_mul_right key hpos

end GlobalTheory.PDivGroup
