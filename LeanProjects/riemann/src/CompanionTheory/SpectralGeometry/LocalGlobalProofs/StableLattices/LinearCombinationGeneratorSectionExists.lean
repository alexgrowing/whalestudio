import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.SecNorm

theorem exists_gen_normalised_along : ∀ {X Y S₀ : Scheme.{0}} {M : LB X}, M.IsLB → ∀ {K K₂ : Type} [Fintype K] [Fintype K₂] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ₂ : K₂ → (S₀ ⟶ X)) (ε₂ : K₂ → ℤ) (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 S₀ → FormEq (fun k => e ≫ φ k) ε φ₂ ε₂ →
    ∀ (t : LB.Gen (LB.LinComb M φ ε)), t.IsGen → ∀ (R : LB.Gen (LB.LinComb M φ₂ ε₂)), R.IsGen →
    ∃ t' : LB.Gen (LB.LinComb M φ ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (s : Z ⟶ S₀) (z : Z) (J : (Z ⟶ X) → M.ι), Good M z J → val t' (s ≫ e) z J = val R s z J := by
  intro X Y S₀ M hM K K₂ _ _ φ ε φ₂ ε₂ p e he hF t ht R hR
  obtain ⟨t', ht', hv⟩ := exists_gen hM (φ' := φ) (ε' := ε)
    (fun U _ h => by
      have c := hF U (fun ψ => h (p ≫ ψ))
      simp only [Category.assoc] at c
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.assoc, c.symm]
      simp)
    (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ t (LB.invGen M _ _ (LB.pullGen M _ _ t (p ≫ e))))
      (LB.pullGen M _ _ R p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hR _))
  refine ⟨t', ht', fun Z s z J hJ => ?_⟩
  have h₁ : (s ≫ e) ≫ p = s := by rw [Category.assoc, he, Category.comp_id]
  have h₂ : (s ≫ e) ≫ p ≫ e = s ≫ e := by rw [← Category.assoc, h₁]
  rw [hv Z (s ≫ e) z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, h₁, h₂, mul_inv_cancel,
    _root_.one_mul]

end GlobalTheory.CompanionTheory.SecNorm
