import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftShearMapSquareZeroAbelianSchemesStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift.Hom

theorem one_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  let x : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
  have e : x * x = x := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 x x rfl rfl, _root_.mul_one]; rfl)
  have e' : x = 1 := by simpa using e
  have := congrArg (fun z ↦ z.left) e'
  refine this.trans ?_
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] (T : Over S) :
    (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem liftHom_sq : AbelianDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I → AbelianSchemeLifts.At hI π → LiftHom (divided₂ hI) π := by
  intro P R R₀ _ _ I hI π hπ hk H g A₀ _ A _ i h hA hg g' B₀ _ B _ j k hB hg' f₀ _ hf
  have pA := (P.1 R A g hA hg).1
  have pB := (P.1 R B g' hB hg').1
  obtain ⟨l, l₁, l₂⟩ : ∃ l : (A₀ ⊗ B₀).left ⟶ (A ⊗ B).left, l ≫ (fst A B).left = (fst A₀ B₀).left ≫ i ∧
      l ≫ (snd A B).left = (snd A₀ B₀).left ≫ j :=
    ⟨Limits.pullback.lift ((fst A₀ B₀).left ≫ i) ((snd A₀ B₀).left ≫ j) (by
      rw [Category.assoc, Category.assoc, h.1.w, k.1.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w]),
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_lift_shearMap_squareZero_abelianSchemes R R₀ I hI π hπ hk H g g' A₀ B₀ A B i j h k hA hB hg hg' A B i j h.1 k.1
    hA.smooth hB.smooth η[A].left η[B].left (Over.w η[A]) (Over.w η[B])
    ((one_left_comp h _).trans (Category.id_comp _)) ((one_left_comp k _).trans (Category.id_comp _)) l l₁ l₂ f₀
    (by rw [schemeFil_eq_liftFil _ h pA, schemeFil_eq_liftFil _ k pB]; exact hf)
  refine GlobalTheory.T.existsUnique_isMonHom_lift_of_grpPullback_abelian R R₀ π hπ ⟨2, hk ▸ hI⟩ A₀ B₀ A B i j h k hA hB f₀ (lift (𝟙 A) 1 ≫ φ) ?_
  have e : i ≫ (lift (𝟙 A) (1 : A ⟶ B)).left = (lift (𝟙 A₀) (1 : A₀ ⟶ B₀)).left ≫ l := by
    refine Limits.pullback.hom_ext ?_ ?_
    · change (i ≫ _) ≫ (fst A B).left = (_ ≫ l) ≫ (fst A B).left
      rw [Category.assoc, Category.assoc, l₁, ← Over.comp_left, ← Category.assoc, ← Over.comp_left, lift_fst, lift_fst,
        Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
    · change (i ≫ _) ≫ (snd A B).left = (_ ≫ l) ≫ (snd A B).left
      rw [Category.assoc, Category.assoc, l₂, ← Over.comp_left, ← Category.assoc, ← Over.comp_left, lift_snd, lift_snd,
        one_left_comp k, one_left, ← Category.assoc, h.1.w, Category.assoc]
  rw [Over.comp_left, ← Category.assoc, e, Category.assoc, hφ, ← Category.assoc, ← Over.comp_left, comp_mul,
    lift_fst_assoc, lift_snd, _root_.mul_one, Category.id_comp]

end GlobalTheory.SqLift.Hom
