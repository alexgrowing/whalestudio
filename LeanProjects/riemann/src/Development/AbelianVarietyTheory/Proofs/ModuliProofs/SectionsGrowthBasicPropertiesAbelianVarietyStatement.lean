import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVariety
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (g : ℕ), M.IsLB → (∃ r, SectionsHaveFiniteDimension P.A.hom M r) ∧ (∀ δ δ', Vol P.A.hom M g δ → Vol P.A.hom M g δ' → δ = δ') ∧ (∀ (M' : LB P.A.left) δ, M'.IsLB → LBIso M M' → Vol P.A.hom M g δ → Vol P.A.hom M' g δ) ∧ (∀ (a : ℕ) δ, 1 ≤ a → Vol P.A.hom M g δ → Vol P.A.hom (lbPow M a) g ((a : ℝ) ^ g * δ)) ∧ (∀ (a : ℕ) δ, 1 ≤ a → Out.RelAmple P.A M → Vol P.A.hom (lbPow M a) g ((a : ℝ) ^ g * δ) → Vol P.A.hom M g δ) ∧ ∀ (M' : LB P.A.left) (s : (LB.div M' M).Sec), M'.IsLB → (∃ j, s.f j ≠ 0) → (∀ r r', SectionsHaveFiniteDimension P.A.hom M r → SectionsHaveFiniteDimension P.A.hom M' r' → r ≤ r') ∧ ∀ δ δ', Vol P.A.hom M g δ → Vol P.A.hom M' g δ' → δ ≤ δ' := by
  first | exact @GlobalTheory.VolBasic.vol_basic | exact GlobalTheory.VolBasic.vol_basic | (intros; apply GlobalTheory.VolBasic.vol_basic <;> assumption)
