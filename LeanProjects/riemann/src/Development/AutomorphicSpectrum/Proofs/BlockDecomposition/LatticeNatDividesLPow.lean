import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatticeUnit

theorem natCast_dvd_pow :
    ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
      Lat.Hyp f ξ l m → ∀ n : ℕ, n ≠ 0 →
        ∃ (k : ℕ) (u : Lat.A f ξ l M), (n : Lat.A f ξ l M) * u = (l : Lat.A f ξ l M) ^ k := by
  intro W B _ _ _ f ξ l M m h n hn
  obtain ⟨k, u, hu⟩ := h.unit n hn
  refine ⟨k, Lat.ofW f ξ l M u, ?_⟩
  rw [← map_natCast (Lat.ofW f ξ l M) n, ← map_mul, hu, map_pow, map_natCast]

end GlobalTheory.CompanionTheory.LatticeUnit
