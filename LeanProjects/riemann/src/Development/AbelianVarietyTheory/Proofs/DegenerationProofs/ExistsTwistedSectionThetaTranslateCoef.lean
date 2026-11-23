import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiCoef

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h : D.c 0 = D.c 0 * D.c 0 := by
    have := D.c_add 0 0
    rwa [add_zero] at this
  have h1 : D.c 0 = 1 := left_eq_mul.1 h
  rw [cT, h1, MonObj.comp_one]

theorem comp_cT {T T' : Over (Spec (CommRingCat.of R))} (r : T ⟶ T') (α : D.X) : r ≫ cT D T' α = cT D T α := by
  rw [← Category.assoc, comp_toUnit]

theorem exists_untwist (χ : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (hu : u.IsGen)
    (g : SecBT D (𝟙_ _) 1 χ) :
    ∃ g₀ : SecBT D (𝟙_ _) 1 0, ∀ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J),
      Good D.P.L z J → sval g₀ (lift (toUnit T) (y * cT D T χ)).left z J =
        sval g (lift (toUnit T) y).left z J * ((val u (toUnit T).left z J * rigV D z J)⁻¹).val := by
  let Y : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let τ : Y ⟶ Y := lift (toUnit Y) (snd _ _ * (cT D Y χ)⁻¹)
  have hF : FormEq
      (Sum.elim (fun k => τ.left ≫ famφT D (𝟙_ _) χ k)
        (fun k => (toUnit Y).left ≫ Sum.elim (fun _ : PUnit => (D.c χ).left) (fun _ : PUnit => eSec D.P.A) k))
      (Sum.elim (DegPre.famε 1) (fun k => -(Sum.elim (fun _ => -1) (fun _ => 1) k)))
      (famφT D (𝟙_ _) 0) (DegPre.famε 1) := by
    intro U _ h
    have e₀ : famφT D (𝟙_ _) 0 0 = famφT D (𝟙_ _) 0 1 := by
      change (snd _ _ : Y ⟶ D.P.A).left = (snd _ _ * cT D Y 0).left
      rw [cT_zero, _root_.mul_one]
    have e₀' : famφT D (𝟙_ _) 0 2 = famφT D (𝟙_ _) 0 3 := by
      change (cT D Y 0).left = (1 : Y ⟶ D.P.A).left
      rw [cT_zero]
    have e₁ : τ.left ≫ famφT D (𝟙_ _) χ 1 = famφT D (𝟙_ _) 0 1 := by
      change (τ ≫ (snd _ _ * cT D Y χ)).left = (snd _ _ * cT D Y 0).left
      rw [cT_zero, _root_.mul_one, MonObj.comp_mul, comp_cT, lift_snd, inv_mul_cancel_right]
    have e₂ : τ.left ≫ famφT D (𝟙_ _) χ 2 = famφT D (𝟙_ _) χ 2 := by
      change (τ ≫ cT D Y χ).left = (cT D Y χ).left
      rw [comp_cT]
    have e₃ : τ.left ≫ famφT D (𝟙_ _) χ 3 = famφT D (𝟙_ _) 0 3 := by
      change (τ ≫ (1 : Y ⟶ D.P.A)).left = (1 : Y ⟶ D.P.A).left
      rw [MonObj.comp_one]
    have e₄ : (toUnit Y).left ≫ (D.c χ).left = famφT D (𝟙_ _) χ 2 := rfl
    have e₅ : (toUnit Y).left ≫ eSec D.P.A = famφT D (𝟙_ _) 0 3 := rfl
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four,
      e₀, e₀', e₁, e₂, e₃, e₄, e₅]
    simp [DegPre.famε, _root_.mul_assoc]
  obtain ⟨g₀, hg₀⟩ := exists_sec D.P.isLB hF (pullMulSec g τ.left
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ u D.rig) (toUnit Y).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hu D.rig_gen) _)))
  refine ⟨g₀, fun T y z J hJ => ?_⟩
  have e₂ : (lift (toUnit T) (y * cT D T χ)).left ≫ τ.left = (lift (toUnit T) y).left := by
    rw [← Over.comp_left]
    congr 1
    refine (comp_lift _ _ _).trans (congrArg₂ lift (toUnit_unique _ _) ?_)
    rw [MonObj.comp_mul, GrpObj.comp_inv, comp_cT, lift_snd, mul_inv_cancel_right]
  have e₃ : (lift (toUnit T) (y * cT D T χ)).left ≫ (toUnit Y).left = (toUnit T).left := by
    rw [← Over.comp_left]
    exact congrArg _ (toUnit_unique _ _)
  rw [hg₀ _ _ z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, e₂, val_inv, val_pull hJ, e₃, val_mul hJ]
  congr 5

theorem exists_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th : SecBT D (𝟙_ _) 1 0), (∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b) → ∀ (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ g : SecBT D (𝟙_ _) 1 χ, ∃ b : R, Coef D χ u th g b := by
  intro R _ _ D th hth χ u hu g
  obtain ⟨g₀, hg₀⟩ := exists_untwist D χ u hu g
  obtain ⟨b, hb⟩ := hth g₀
  refine ⟨b, fun T y z J hJ => ?_⟩
  have e₁ : (lift (toUnit T) (y * cT D T χ)).left ≫ (𝟙_ _ ⊗ D.P.A).hom = T.hom := Over.w _
  have h := hb _ (lift (toUnit T) (y * cT D T χ)).left z J hJ
  rw [e₁, hg₀ T y z J hJ, Units.mul_inv_eq_iff_eq_mul] at h
  rw [h]
  ring

end GlobalTheory.PsiCoef
