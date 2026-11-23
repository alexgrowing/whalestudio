import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValueAtMultipleOfBaseChangedGenerator
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_at_multiple_of_baseChanged_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (T Ω : Type) [CommRing T] [IsReduced T] [Algebra c.F T] [Field Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (z₀ : FrPt Xo c T) (z₁ : FrPt Xo c Ω) (a₀ : T), z₁.x = spMap χ.toRingHom ≫ z₀.x → (∀ τ j, z₁.u τ j = spMap (dualMap χ.toRingHom) ≫ z₀.u τ j) → SecBC χ.toRingHom a₀ z₀.x z₁.x z₀.s z₁.s → evR Xo c f z₁ = χ (a₀ ^ n * evR Xo c f z₀) := by
  first | exact @GlobalTheory.HkValueMul.evR_of_secBC_mul | exact GlobalTheory.HkValueMul.evR_of_secBC_mul | (intros; apply GlobalTheory.HkValueMul.evR_of_secBC_mul <;> assumption)
