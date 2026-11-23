import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGermsZeroFiniteFreeBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_germs_zero_finiteFree_baseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U → (∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z = x → ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0 := by
  first | exact @GlobalTheory.Mum.FreeCoord.germ_eq_zero | exact GlobalTheory.Mum.FreeCoord.germ_eq_zero | (intros; apply GlobalTheory.Mum.FreeCoord.germ_eq_zero <;> assumption)
