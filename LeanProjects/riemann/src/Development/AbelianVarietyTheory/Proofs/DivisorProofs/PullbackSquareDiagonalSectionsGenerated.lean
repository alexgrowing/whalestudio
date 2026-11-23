import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RigPull

theorem hasGen_pull_of_comm {X₀ X Y Y₀ : Scheme.{0}} {L : LB X₀} (hL : L.IsLB) (F : X ⟶ X₀) {a : Y₀ ⟶ X₀}
    {a' : Y ⟶ X} {ψ : Y ⟶ Y₀} (e : a' ≫ F = ψ ≫ a) (h : HasGen (L.pull a)) : HasGen ((L.pull F).pull a') := by
  refine (CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hL F) a')).1 ?_
  have h0 : CechPic.cls _ (pull_isLB hL a) = 0 := (CechPic.cls_eq_zero_iff (pull_isLB hL a)).2 h
  rw [CechPic.cls_pull (pull_isLB hL F) a', CechPic.cls_pull hL F, ← CechPic.pull_comp, e, CechPic.pull_comp,
    ← CechPic.cls_pull hL a (pull_isLB hL a), h0, map_zero]

end GlobalTheory.RigPull

namespace GlobalTheory

open RigPull SiegelDescent

theorem hasGen_pull_rig_of_isGrpPullback : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ c : 𝔠.elt, HasGen (((X.P c).pull φ₂).pull (lift (1 : A' ⟶ A') (𝟙 A')).left) ∧
      HasGen (((X.P c).pull φ₂).pull (lift (𝟙 A') (1 : A' ⟶ A')).left) := by
  intro F _ _ 𝔠 S S' X b A' _ _ φ hp φ₂ sq c
  have hφ : φ ≫ X.A.hom = A'.hom ≫ b := hp.1.w
  have one := one_comp hp A' X.A φ hφ
  have idφ : (𝟙 A' : A' ⟶ A').left ≫ φ = φ ≫ (𝟙 X.A : X.A ⟶ X.A).left := by simp
  exact ⟨hasGen_pull_of_comm (X.isLB c) φ₂ (lift_square sq one idφ) (X.rig₁ c),
    hasGen_pull_of_comm (X.isLB c) φ₂ (lift_square sq idφ one) (X.rig₂ c)⟩

end GlobalTheory
