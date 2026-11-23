import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationComapSpanPowStatement

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Lat

theorem quot_pdP_no_torsion : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ (r : ℕ) (x : Lat.A f ξ l M), (l : Lat.A f ξ l M) * x ∈ pdP (Lat.γ f ξ l M hc) r → x ∈ pdP (Lat.γ f ξ l M hc) r := by
  intro W B _ _ _ f ξ l M m hH hc r x hx
  rw [GlobalTheory.T.lattice_filtration_comap_span_pow f ξ l M m hH hc r] at hx ⊢
  rw [Ideal.mem_comap, map_mul, map_natCast] at hx
  rw [Ideal.mem_comap]
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hH.l0 Nat.cast_zero
  have hl : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl0
  have hu : algebraMap ℚ B (l : ℚ)⁻¹ * (l : B) = 1 := by
    rw [← map_natCast (algebraMap ℚ B) l, ← map_mul, inv_mul_cancel₀ hl, map_one]
  have h2 := Ideal.mul_mem_left _ (algebraMap ℚ B (l : ℚ)⁻¹) hx
  rwa [← mul_assoc, hu, one_mul] at h2

end GlobalTheory.CompanionTheory.Lat
