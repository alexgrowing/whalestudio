import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeNormMembership
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
open ReciprocityTheory.ChartRestriction.G.Geo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_norm_membership : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (q : ℕ) (x : Ω), (∀ (c : (k : K) → ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ W : ValuationSubring Ω, (∀ p, y p / y ⟨p.1, c p.1⟩ ∈ W) → x * (u * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ q ∈ W) → x * u ^ q ∈ chartLatNm y a q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartVal.mem_chartLatNm_of_forall_valuationSubring | exact GlobalTheory.CompanionTheory.Ar.ChartVal.mem_chartLatNm_of_forall_valuationSubring | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartVal.mem_chartLatNm_of_forall_valuationSubring <;> assumption)
