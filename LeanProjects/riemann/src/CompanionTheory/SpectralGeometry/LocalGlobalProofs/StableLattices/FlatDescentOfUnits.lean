import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FnDesc

theorem exists_app_eq_of_lfp {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π]
    [LocallyOfFinitePresentation π] (U : Y.Opens) (f : Γ(X, π ⁻¹ᵁ U))
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (h₁ : ⊤ ≤ g₁ ⁻¹ᵁ (π ⁻¹ᵁ U))
      (h₂ : ⊤ ≤ g₂ ⁻¹ᵁ (π ⁻¹ᵁ U)), g₁ ≫ π = g₂ ≫ π →
      (g₁.appLE _ ⊤ h₁).hom f = (g₂.appLE _ ⊤ h₂).hom f) :
    ∃ a, (π.app U).hom a = f := by
  have : Surjective (π ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  have p := isPullback_morphismRestrict π U
  have : Flat (π ∣_ U) := MorphismProperty.of_isPullback (P := @Flat) p.flip ‹_›
  have : LocallyOfFinitePresentation (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) p.flip ‹_›
  obtain ⟨b, hb⟩ := GlobalTheory.FunDescent.exists_appTop_eq (π ∣_ U) ((GlobalTheory.FunDescent.res (π ⁻¹ᵁ U)).hom f) (by
    intro Z g₁ g₂ e
    have k : ∀ g : Z ⟶ (π ⁻¹ᵁ U).toScheme, ⊤ ≤ (g ≫ (π ⁻¹ᵁ U).ι) ⁻¹ᵁ (π ⁻¹ᵁ U) := by
      intro g; simp
    have := hf Z (g₁ ≫ (π ⁻¹ᵁ U).ι) (g₂ ≫ (π ⁻¹ᵁ U).ι) (k _) (k _) (by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% e])
    rw [← GlobalTheory.FunDescent.res_comp_appTop _ g₁ _ rfl, ← GlobalTheory.FunDescent.res_comp_appTop _ g₂ _ rfl] at this
    exact this)
  obtain ⟨a, rfl⟩ := (GlobalTheory.FunDescent.res_bijective U).2 b
  refine ⟨a, (GlobalTheory.FunDescent.res_bijective _).1 ?_⟩
  rw [← GlobalTheory.FunDescent.res_square_apply, hb]

theorem units_descend :
    ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f → ∀ V : Q.Opens,
    Function.Injective (pullU f V) ∧ ∀ a : Γ(P, f ⁻¹ᵁ V)ˣ,
      (∀ (W : Scheme.{0}) (b c : W ⟶ P), b ≫ f = c ≫ f → ∀ w : W, f (b w) ∈ V →
        gm b w (f ⁻¹ᵁ V) a = gm c w (f ⁻¹ᵁ V) a) → ∃ s : Γ(Q, V)ˣ, pullU f V s = a := by
  intro P Q f _ _ _ V
  refine ⟨fun a b h => Units.ext (GlobalTheory.FunDescent.app_injective f V (congrArg Units.val h)), fun a ha => ?_⟩
  obtain ⟨t, ht⟩ := exists_app_eq_of_lfp f V a.val (fun Z g₁ g₂ h₁ h₂ e => by
    have k : ∀ (g : Z ⟶ P) (h : ⊤ ≤ g ⁻¹ᵁ (f ⁻¹ᵁ V)) (z : Z),
        gm (𝟙 Z) z ⊤ (res h (pullU g _ a)) = gm g z (f ⁻¹ᵁ V) a := fun g h z =>
      (gm_res (𝟙 Z) z h trivial _).trans ((gm_pull (𝟙 Z) g z _ (h trivial) _).trans (by
        rw [Category.id_comp]))
    have : res h₁ (pullU g₁ _ a) = res h₂ (pullU g₂ _ a) := unit_ext fun z _ =>
      (k g₁ h₁ z).trans ((ha Z g₁ g₂ e z (h₁ trivial)).trans (k g₂ h₂ z).symm)
    exact congrArg Units.val this)
  obtain ⟨s, rfl⟩ := GlobalTheory.FunDescent.isUnit_of_isUnit_app f V t (ht ▸ a.isUnit)
  exact ⟨s, Units.ext ht⟩

end GlobalTheory.CompanionTheory.FnDesc
