import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPoinc.USum

theorem ptSecT_comp_whisker {B : Scheme.{0}} {A : Over B} [GrpObj A] {T T' : Over B} (c : T' ⟶ T) (y : T ⟶ A) :
    (ptSecT A (c ≫ y)).left ≫ (c ▷ A).left = c.left ≫ (ptSecT A y).left := by
  rw [← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT, lift_whiskerRight, comp_lift, Category.id_comp,
    Category.comp_id]

theorem isTwVal_pull {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀))
    {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1)))
    (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) {T' : Over B} (c : T' ⟶ T) :
    IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ (c ≫ β) (c ≫ x) (c ≫ h) (c.left.appTop.hom v) := by
  rintro ⟨α, U, hα, hU, H⟩
  obtain ⟨α', hα', vα⟩ := GlobalTheory.VVRank.exists_gen_pullTo
    (φ' := ![(snd T' P.A).left, (snd T' P.A ^ m).left]) α hα (c ▷ P.A).left (fun k => by
      fin_cases k
      · exact GlobalTheory.VVRank.whisker_snd_left P.A c
      · change (c ▷ P.A).left ≫ (snd T P.A ^ m).left = (snd T' P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, whiskerRight_snd])
  obtain ⟨U', hU', vU⟩ := GlobalTheory.SymLiftGlobal.exists_symLift_pull_val P.isLB c hU
  refine ⟨α', U', hα', hU', fun Z r z J hJ => ?_⟩
  have eq₁ : (c ≫ x) * (c ≫ h) = c ≫ (x * h) := (MonObj.comp_mul _ _ _).symm
  have q := H Z (r ≫ c.left) z J hJ
  have g : gs r z ⊤ (c.left.appTop.hom v) = gs (r ≫ c.left) z ⊤ v := gs_pull r c.left z ⊤ trivial v
  have w : ∀ (y : T ⟶ P.A) {W : Scheme.{0}} (k : (T ⊗ P.A).left ⟶ W),
      (ptSecT P.A (c ≫ y)).left ≫ (c ▷ P.A).left ≫ k = c.left ≫ (ptSecT P.A y).left ≫ k := fun y W k => by
    rw [← Category.assoc, ptSecT_comp_whisker, Category.assoc]
  have eq₃ : (c ≫ (x * h)) ^ m = c ≫ (x * h) ^ m := (MonObj.comp_pow _ _ _).symm
  rw [g, vα _ _ z J hJ, vα _ _ z J hJ, vU _ _ z J hJ, eq₁, eq₃]
  simp only [Category.assoc, ptSecT_comp_whisker, comp_whiskerRight, Over.comp_left, w]
  simpa only [Category.assoc] using q

end GlobalTheory.UPoinc.USum
