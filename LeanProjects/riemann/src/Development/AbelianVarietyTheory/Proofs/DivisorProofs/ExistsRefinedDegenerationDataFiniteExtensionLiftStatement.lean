import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRefinedDegenerationDataFiniteExtensionLift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_refined_degenerationData_finiteExtension_lift : ∀ g n : ℕ, ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ (Y : Scheme.{0}) (q : Y ⟶ F.X), IsFinite q → Surjective q → ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X) (y : Sp (FractionRing V₁) ⟶ F.X) (y' : Sp (FractionRing V₁) ⟶ Y), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Refines Q ρ D₀.toPre e₀ ∧ y ≫ i = jK V₁ ≫ spMap ρ ≫ ξ ∧ y' ≫ q = y := by
  first | exact @GlobalTheory.Poinc.Sep.SharpExt.exists_refined_ext_lift | exact GlobalTheory.Poinc.Sep.SharpExt.exists_refined_ext_lift | (intros; apply GlobalTheory.Poinc.Sep.SharpExt.exists_refined_ext_lift <;> assumption)
