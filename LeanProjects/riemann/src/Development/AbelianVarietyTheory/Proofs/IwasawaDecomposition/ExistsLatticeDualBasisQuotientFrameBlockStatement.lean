import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeDualBasisQuotientFrameBlock
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_dualBasisQuotientFrameBlock : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (ι : Type) (m k : ι → ℕ) (S : Fr M m k) (τ : ι) (A₀ : Mat m Ω), A₀ ∈ S.S (genericPoint M.Z) → ∃ EE : M.Lat (Rest m k τ), ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  first | exact @GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock | exact GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock | (intros; apply GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock <;> assumption)
