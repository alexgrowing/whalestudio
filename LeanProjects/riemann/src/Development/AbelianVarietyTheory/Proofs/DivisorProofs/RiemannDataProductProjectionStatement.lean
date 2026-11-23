import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannDataProductProjection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_data_product_projection : ∀ (S : Scheme.{0}) (P P₁ P₂ : PPAS S) (π₁ : P.A ⟶ P₁.A) (π₂ : P.A ⟶ P₂.A), IsMonHom π₁ → IsMonHom π₂ → P.c = CechPic.pull (π₁ ⊗ₘ π₁).left P₁.c + CechPic.pull (π₂ ⊗ₘ π₂).left P₂.c → ∀ (y : Sp ℂ ⟶ S) (d : P.RiemannData y) (d₁ : P₁.RiemannData y) (d₂ : P₂.RiemannData y), ∃ (Q₁ : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P₁.g → ℂ)) (Q₂ : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P₂.g → ℂ)), (∀ z, (d₁.u.ex (Q₁ z)).left ≫ d₁.φ = (d.u.ex z).left ≫ d.φ ≫ π₁.left) ∧ (∀ z, (d₂.u.ex (Q₂ z)).left ≫ d₂.φ = (d.u.ex z).left ≫ d.φ ≫ π₂.left) ∧ ∀ z w, HermFrame.form d.H z w = HermFrame.form d₁.H (Q₁ z) (Q₁ w) + HermFrame.form d₂.H (Q₂ z) (Q₂ w) := by
  first | exact @GlobalTheory.RiemProd.exists_lin_add | exact GlobalTheory.RiemProd.exists_lin_add | (intros; apply GlobalTheory.RiemProd.exists_lin_add <;> assumption)
