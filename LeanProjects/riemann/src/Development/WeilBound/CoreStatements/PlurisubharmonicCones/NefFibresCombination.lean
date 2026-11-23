import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GeoNumOneLin

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem LevelTowerAlt.nef_fibres_combination : PB.Inputs → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (a a' : K → ℤ) (p q : ℕ), NefOnFibres P a → (∀ k, 0 ≤ a' k) → NefOnFibres P ((q : ℤ) • a + (p : ℤ) • a') := by
  intro _ K _ J _ P a a' p q hP ha' W hW hPW hc hdim
  obtain ⟨d, hd0, hlin⟩ := LevelTowerAlt.geoNum_one_lin W
  have h1 := hP W hW hPW hc hdim
  rw [hlin] at h1 ⊢
  have h2 : 0 ≤ ∑ k, a' k * d k := Finset.sum_nonneg fun k _ => mul_nonneg (ha' k) (hd0 k)
  have h3 : ∑ k, ((q : ℤ) • a + (p : ℤ) • a') k * d k = (q : ℤ) * ∑ k, a k * d k + (p : ℤ) * ∑ k, a' k * d k := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
  rw [h3]
  exact add_nonneg (mul_nonneg (Int.natCast_nonneg q) h1) (mul_nonneg (Int.natCast_nonneg p) h2)
