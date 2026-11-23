import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.TwoData

theorem exists_scalar_matrix : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (th th' : P.L.Sec) (v v' : Fin P.g → (epsR K ⟶ P.A)), (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th) → (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th') → IsLieBasis v → IsLieBasis v' → ∃ (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), a ≠ 0 ∧ (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) ∧ ∀ i, IsLieComb (M i) v (v' i) := by
  intro K _ P th th' v v' hth hth' hv hv'
  obtain ⟨b, hb⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.principalPolarisation_exists_unique_section GlobalTheory.abelianSchemeLaws_all.2.secTwist P
  obtain ⟨a, ha, -⟩ := hb th
  obtain ⟨a', ha', -⟩ := hb th'
  choose M hM using fun i => (hv.2 _ (hv'.1 i)).exists
  have hne : ∀ (s : P.L.Sec) (c : K), (∀ s' : Sp K, ∃ z : P.A.left, P.A.hom z = s' ∧ z ∈ Out.nonzeroLocus s) →
      (∀ i, s.f i = Geo.Tor.constFn P.A.hom _ c * b.f i) → c ≠ 0 := by
    rintro s c hs hc rfl
    obtain ⟨z, -, hz⟩ := hs (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    rw [hc i, Geo.Tor.constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  have h0 := hne th a hth ha
  have h0' := hne th' a' hth' ha'
  refine ⟨a' * a⁻¹, M, mul_ne_zero h0' (inv_ne_zero h0), fun i => ?_, hM⟩
  rw [ha' i, ha i, ← _root_.mul_assoc, Geo.Tor.constFn, Geo.Tor.constFn, Geo.Tor.constFn, ← map_mul, ← map_mul, inv_mul_cancel_right₀ h0]

end GlobalTheory.MBLow.TwoData
