import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFlagPointInOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariantStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsUpperOfMinors
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointTriangularChangeOrbit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentFamilyAnalytic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PlkFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type)
    [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d)
    (τ : Ψ) (ca cb : Fin N) (hab : ca < cb) (hblk : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (l : Fin BM.q)
    (x₀ : FA.Re.R.X) (hO : FA.pr (FA.Re.π x₀) ∈ BM.O l)
    (hplk : ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FA.Re.R.lift x₀ x₀) p ≠ 0) :
    ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), SameOrbit (FA.Re.R.lift x₀ x₀)
      (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FC.Lca τ ca cb c a)) := by
  have hz : FA.Re.R.lift x₀ x₀ ∈ mcPts (mCoordIdeal y) := FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀)
  obtain ⟨h, hh, horb⟩ := GlobalTheory.T.exists_flag_point_in_orbit K ι Φ y Ψ N j M n BM l _ hO _ hz (FA.pr_eq x₀)
  obtain ⟨hbm, hbg, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l _ hO
  have hmin : ∀ τ' (i : Fin N), IsProperStep N j i →
      minorIJ (h τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
    intro τ' i hi
    obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
      Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    have h1 := (GlobalTheory.T.plucker_nonvanishing_orbit_invariant K ι Φ y Ψ N j M (BM.F l) _ _ _ (τ', i) horb).1 (hplk (τ', i))
    rwa [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_flagPt K ι Φ y Ψ N j M (BM.F l) _ h (τ', i) k (BM.isFrame l) hbm hbg
      (fun τ'' => (hh τ'').1) hk] at h1
  choose B hBd hBt hBdet hBL using fun τ' =>
    GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell.exists_upper_of_minors N j (h τ') M.j_le (hh τ').1 (hh τ').2 (hmin τ')
  obtain ⟨-, -, hlc, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main Ψ N j τ ca cb hab hblk
  have hL : ∀ τ', IsBlockDiag j (h τ' * B τ') ∧ IsLowerUni (h τ' * B τ') := by
    intro τ'
    refine ⟨fun r s hrs => ?_, hBL τ'⟩
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : ((r : ℕ) < N - j ↔ (t : ℕ) < N - j)
    · rw [hBd τ' t s (fun e => hrs (ht.trans e)), mul_zero]
    · rw [(hh τ').1 r t ht, zero_mul]
  obtain ⟨c, a, e⟩ := hlc _ hL
  refine ⟨c, a, ?_⟩
  rw [e]
  exact orbit_trans horb (orbit_symm
    (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.sameOrbit_flagPt_mul K ι Φ y Ψ N j M (BM.F l) _ h B fun τ' => ⟨hBd τ', hBt τ', hBdet τ'⟩))
