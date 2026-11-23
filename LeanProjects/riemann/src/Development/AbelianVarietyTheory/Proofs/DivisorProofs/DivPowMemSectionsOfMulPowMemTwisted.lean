import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivMemOfMulPowDivMemOfRegularPair
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.VolBr

theorem Pair.div_pow_mem_H_of_mul_pow_sub : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ,
    ∀ (N m : ℕ) (u : X.functionField), u ∈ P.H N (m - c) → u * t ^ N / s ^ m ∈ P.H 0 (b * N - c) →
    u / s ^ m ∈ P.H N (-c) := by
  intro k _ X _ p D _ P b s t hG c N m u hu hut x i j hi hj
  let O : Subring X.functionField := (algebraMap (X.presheaf.stalk x) X.functionField).range
  have hO : ∀ f, RegAt x f ↔ f ∈ O := fun f => Iff.rfl
  have hri : (P.r i : X.functionField) ≠ 0 := (P.r i).ne_zero
  have hrj : (P.r' j : X.functionField) ≠ 0 := (P.r' j).ne_zero
  have hs : P.loc 0 1 s i j ∈ O := (hO _).1 (hG.s_mem.1 x i j hi hj)
  have ht : P.loc (-1) b t i j ∈ O := (hO _).1 (hG.t_mem.1 x i j hi hj)
  have hs0 : P.loc 0 1 s i j ≠ 0 := by
    simp only [Pair.loc, zpow_zero, zpow_one, mul_one]
    exact mul_ne_zero hG.s_ne hrj
  have hreg : ∀ g ∈ O, g * P.loc (-1) b t i j / P.loc 0 1 s i j ∈ O → g / P.loc 0 1 s i j ∈ O :=
    fun g hg h => (hO _).1 (hG.reg x i j hi hj g ((hO _).2 hg) ((hO _).2 h))
  have hg : P.loc N ((m : ℤ) - c) u i j ∈ O := (hO _).1 (hu x i j hi hj)
  have e1 : P.loc N ((m : ℤ) - c) u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m =
      P.loc 0 ((b : ℤ) * N - c) (u * t ^ N / s ^ m) i j := by
    simp only [Pair.loc, zpow_zero, zpow_one, mul_one, zpow_sub₀ hrj, zpow_neg, mul_pow, inv_pow, zpow_natCast]
    rw [show ((b : ℤ) * N) = ((b * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]
    field_simp
  have e2 : P.loc N ((m : ℤ) - c) u i j / P.loc 0 1 s i j ^ m = P.loc N (-c) (u / s ^ m) i j := by
    simp only [Pair.loc, zpow_zero, zpow_one, mul_one, zpow_sub₀ hrj, zpow_neg, mul_pow, zpow_natCast]
    field_simp
  have hgN : P.loc N ((m : ℤ) - c) u i j * P.loc (-1) b t i j ^ N / P.loc 0 1 s i j ^ m ∈ O := by
    rw [e1]
    exact (hO _).1 (hut x i j hi hj)
  have := regularPair_pow X.functionField O _ _ hs ht hs0 hreg m N _ hg hgN
  rw [e2] at this
  exact (hO _).2 this

end GlobalTheory.VolBr
