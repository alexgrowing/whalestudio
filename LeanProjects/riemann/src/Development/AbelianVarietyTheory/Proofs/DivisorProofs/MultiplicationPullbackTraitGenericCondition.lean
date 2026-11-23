import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem gs_scal_over_self {W : Type} [CommRing W] {X Z : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of W)) (g : X ⟶ X)
    (hg : g ≫ q = q) (p : Z ⟶ X) (z : Z) (a : W) :
    gs (p ≫ g) z ⊤ (scal q a) = gs p z ⊤ (scal q a) := by
  have e : (g.app ⊤).hom (scal q a) = scal q a := by
    have e' : scal (g ≫ q) a = (g.app ⊤).hom (scal q a) := rfl
    rw [← e', hg]
  exact (gs_pull p g z ⊤ trivial (scal q a)).symm.trans (congrArg (gs p z ⊤) e)

theorem pullMul_trait_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ) (a : W)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J, Good C.P.L.L z J →
      sval S p z J = (val u (p ≫ C.α) z J).val * sval θ₀ (p ≫ (mulA C.A.A m).left) z J) →
    ∀ (σ : SecK C.P.L.L T.β 1) (σ₂ : SecK C.P.L.L T.β (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval θ₀ p' z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ₂ p z J = gs p z ⊤ (scal T.G.hom a) * sval S p' z J := by
  intro R _ _ _ D C W _ _ _ T m a u θ₀ S hS σ σ₂ hσ hσ₂ Z p p' hp z J hJ
  have e1 := GlobalTheory.ZH.TorsFrame.mulA_comm T.cart m
  have e2 := GlobalTheory.ZH.TorsFrame.mulA_comm C.α_cart m
  have h : (p ≫ (mulA T.G m).left) ≫ T.β = (p' ≫ (mulA C.A.A m).left) ≫ C.α := by
    rw [Category.assoc, Category.assoc, e1, e2, ← Category.assoc, hp, Category.assoc]
  rw [hσ₂ Z p z J hJ, hσ Z _ _ h z J hJ, hS Z p' z J hJ, hp,
    gs_scal_over_self T.G.hom _ (Over.w (mulA T.G m)) p z a]
  exact mul_left_comm _ _ _

end GlobalTheory.Mum
