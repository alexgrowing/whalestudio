import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeLinearFormPositivity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_linear_form_positivity : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (ℓ : LinearMap.BilinForm ℤ P.D.toPre.X →ₗ[ℤ] ℤ), IsCN R → P.TorsionIso → InCone P.D.toPre γ → (∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, (∀ y z, be y z = be z y) → ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal be = ∑ i, c i • toReal (γ i) → 0 ≤ ℓ be) → ∃ h : R, h ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (g : R →+* W) (be : LinearMap.BilinForm ℤ P.D.toPre.X), (∀ y z, be y z = be z y) → FormAt P.D.toPre g ϖ be → ∃ n : ℕ, (n : ℤ) = ℓ be ∧ Associated (g h) (ϖ ^ n) := by
  first | exact @GlobalTheory.TorRef.exists_monomial_order_linForm | exact GlobalTheory.TorRef.exists_monomial_order_linForm | (intros; apply GlobalTheory.TorRef.exists_monomial_order_linForm <;> assumption)
