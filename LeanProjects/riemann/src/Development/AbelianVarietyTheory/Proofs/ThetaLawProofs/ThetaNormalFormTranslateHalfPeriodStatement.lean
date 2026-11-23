import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaNormalFormTranslateHalfPeriod
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaNormalForm_translate_halfPeriod : Out.Laws → ThetaUnifAV → ∀ (x x' : KeyIn ℂ) (g : ℕ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b a' b' : Fin g → ℂ) (m n : Fin g → ℤ) (ν : ℂˣ), charHalf g a b → charHalf g a' b' → Wit x h u τ a b → (∀ i, ∃ k : ℤ, a' i = a i + n i / 2 + k) → (∀ i, ∃ k : ℤ, b' i = b i + m i / 2 + k) → IsTrl x' x (u.ex (frac τ 2 m n)) ν → ∃ (h' : x'.P.g = g) (u' : HolUnif x'.P.A x'.P.L g) (φ : x'.P.A ≅ x.P.A) (c : ℂ), IsMonHom φ.hom ∧ (∀ z, u'.ex z ≫ φ.hom = u.ex z) ∧ c ^ 8 * (ν : ℂ) ^ 2 = 1 ∧ (∀ z, z ∈ u'.Λ ↔ z ∈ u.Λ) ∧ u'.IsRig x'.rig ∧ u'.IsFn x'.th (fun z => c * thetaChar τ a' b' z) ∧ ∀ i : Fin g, u'.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x'.v (i.cast h'.symm)) := by
  first | exact @GlobalTheory.HalfTranslate.normalForm_translate | exact GlobalTheory.HalfTranslate.normalForm_translate | (intros; apply GlobalTheory.HalfTranslate.normalForm_translate <;> assumption)
