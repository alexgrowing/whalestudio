import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

noncomputable section
namespace GlobalTheory.DiagAmpleBC

theorem diag_comp {S T : Scheme.{0}} (A : Over S) (B : Over T) (β : B.left ⟶ A.left)
    (β₂ : (G2 B).left ⟶ (G2 A).left) (hs : IsSquare β β₂) :
    (lift (𝟙 B) (𝟙 B)).left ≫ β₂ = β ≫ (lift (𝟙 A) (𝟙 A)).left := by
  have h1 : (lift (𝟙 B) (𝟙 B)).left ≫ (fst B B).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h2 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h3 : (lift (𝟙 B) (𝟙 B)).left ≫ (snd B B).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  have h4 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  apply pullback.hom_ext
  · show _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hs.1, ← Category.assoc, h1, Category.assoc, h2, Category.id_comp, Category.comp_id]
  · show _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hs.2, ← Category.assoc, h3, Category.assoc, h4, Category.id_comp, Category.comp_id]

theorem relAmple_diag_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (t : T ⟶ S) (B : Over T) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsPullback β B.hom A.hom t → IsSquare β β₂ → RelAmple B ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) := by
  intro S T A _ hA P hP hD t B β β₂ hpb hs
  haveI := hA.proper
  have e₁ : LBIso ((P.pull β₂).pull (lift (𝟙 B) (𝟙 B)).left) (P.pull ((lift (𝟙 B) (𝟙 B)).left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP β₂)) _
  have e₂ : LBIso ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull β) (P.pull (β ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
  rw [diag_comp A B β β₂ hs] at e₁
  have e := LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂.symm
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull hpb (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e hD

end GlobalTheory.DiagAmpleBC
