import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

private lemma prime_le_succ_of_dvd_minkM' {n p : ℕ} (hp : p.Prime) (h : p ∣ minkM n) : p ≤ n + 1 := by
  have h' : p ∣ ∏ q ∈ (Finset.range (n + 2)).filter Nat.Prime, q ^ Formalism.HermitianLatticeCounting.S6.minkowskiExp n q := h
  rcases (Prime.dvd_finset_prod_iff hp.prime _).1 h' with ⟨q, hq, hdvd⟩
  rw [Finset.mem_filter, Finset.mem_range] at hq
  have hpq := (Nat.prime_dvd_prime_iff_eq hp hq.2).1 (hp.dvd_of_dvd_pow hdvd)
  omega

theorem dGamSmooth_of_dvd {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u,
      ((Fm.D x i).mem u).C.DGam ∣ minkM (2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m)) :
    Pk.DGamSmooth Fm := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx i u p hp hpd => prime_le_succ_of_dvd_minkM' hp (dvd_trans hpd (hx0 x hx i u))⟩

end Formalism.MainNotions.J
