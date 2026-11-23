import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nefFib_pow_iff' : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (L : HermLB p) (m : ℕ), 0 < m → (ArInt.NefFib (L.pow m) ↔ ArInt.NefFib L) := by
  first | exact @GlobalTheory.ArInt.nefFib_pow_iff | exact GlobalTheory.ArInt.nefFib_pow_iff | (intros; apply GlobalTheory.ArInt.nefFib_pow_iff <;> assumption)
