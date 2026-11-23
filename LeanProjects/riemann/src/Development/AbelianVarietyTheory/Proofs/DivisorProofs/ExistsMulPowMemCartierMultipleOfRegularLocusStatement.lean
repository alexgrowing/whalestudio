import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPowMemCartierMultipleOfRegularLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_pow_mem_cartierMultiple_of_regular_locus : ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] (D : CartierDiv Y) (k : ℕ) (s : Y.functionField), s ∈ Sec D k → ∀ g : Y.functionField, (∀ y ∈ locus D k s, RegAt y g) → ∃ n : ℕ, g * s ^ n ∈ Sec D (k * n) := by
  first | exact @GlobalTheory.Desc.exists_mul_pow_mem_sec | exact GlobalTheory.Desc.exists_mul_pow_mem_sec | (intros; apply GlobalTheory.Desc.exists_mul_pow_mem_sec <;> assumption)
