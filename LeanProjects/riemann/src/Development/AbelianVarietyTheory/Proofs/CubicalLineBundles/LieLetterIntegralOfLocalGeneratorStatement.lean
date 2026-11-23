import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralOfLocalGenerator
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLetter_integral_of_local_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (p : HeightOneSpectrum (𝓞 o.K₁)) (M : Matrix (Fin o.xB.P.g) (Fin o.xB.P.g) o.K₁), IsModelAt o.B o.xB o.φB p M → ∀ (k : Fin o.xB.P.g) (cl : o.K₁), IsLocGen p cl (L.ℓ k).I → ∀ m, p.valuation o.K₁ (Matrix.vecMul (cl • L.U k) M⁻¹ m) ≤ 1 := by
  first | exact @GlobalTheory.LamF.letter_integral_of_isLocGen | exact GlobalTheory.LamF.letter_integral_of_isLocGen | (intros; apply GlobalTheory.LamF.letter_integral_of_isLocGen <;> assumption)
