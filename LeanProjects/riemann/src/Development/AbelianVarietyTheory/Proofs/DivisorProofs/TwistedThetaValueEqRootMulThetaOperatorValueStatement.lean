import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueEqRootMulThetaOperatorValue
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] [ArithBase o' Ω'] {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left) (x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)), IsGenLab ρ ρ' lab φ P₀ a a' x → ∀ (m : ℕ), S'.N = m ^ 2 → ∀ (κ x₀ : S.Gam) (h : S'.Gam), m • h = lab κ → ∃ ξ : Ω', (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ (t : S'.Gam) (v : Ω'), IsTwVal ρ.P S'.N m ρ.th₁ (ρ.fr κ) (genTo _) (x (S'.r • t)) (x h) ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom v) → v * S'.th (lab x₀) = ξ * φ (S.th x₀) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := by
  first | exact @GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul | exact GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul | (intros; apply GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul <;> assumption)
