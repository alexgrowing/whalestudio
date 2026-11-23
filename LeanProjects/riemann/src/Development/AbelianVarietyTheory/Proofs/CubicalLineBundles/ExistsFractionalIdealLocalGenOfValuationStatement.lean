import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFractionalIdealLocalGenOfValuation
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fractionalIdeal_localGen_of_valuation : ∀ (K : Type) [Field K] [NumberField K] (oa : HeightOneSpectrum (𝓞 K) → ℤ), (Function.support oa).Finite → ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧ ∀ (p : HeightOneSpectrum (𝓞 K)) (a : K), p.valuation K a = WithZero.exp (-oa p) → IsLocGen p a I := by
  first | exact @GlobalTheory.LamF.exists_fractionalIdeal_isLocGen_of_valuation | exact GlobalTheory.LamF.exists_fractionalIdeal_isLocGen_of_valuation | (intros; apply GlobalTheory.LamF.exists_fractionalIdeal_isLocGen_of_valuation <;> assumption)
