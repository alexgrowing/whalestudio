import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SplitTorusHom

variable {S : Scheme.{0}}

theorem appTop_comp {A B C : Over S} (a : A ⟶ B) (b : B ⟶ C) (r : Γ(C.left, ⊤)) :
    (a ≫ b).left.appTop.hom r = a.left.appTop.hom (b.left.appTop.hom r) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

theorem appTop_id {A : Over S} (r : Γ(A.left, ⊤)) : (𝟙 A : A ⟶ A).left.appTop.hom r = r := by
  rw [Over.id_left, Scheme.Hom.id_appTop]
  rfl

variable {X X' : Type} [AddCommGroup X] [AddCommGroup X']

theorem appTop_mul_charUnit {Z : Over S} (a b : Z ⟶ splitTorus S X) (χ : X) :
    (a * b).left.appTop.hom (charUnit S X χ).val =
      a.left.appTop.hom (charUnit S X χ).val * b.left.appTop.hom (charUnit S X χ).val := by
  rw [← splitTorusPointsEquiv_val, ← splitTorusPointsEquiv_val, ← splitTorusPointsEquiv_val,
    map_mul]
  rfl

theorem charUnit_add (x y : X) :
    (charUnit S X (x + y)).val = (charUnit S X x).val * (charUnit S X y).val := by
  have h (z : X) := (splitTorusPointsEquiv_val S X _ (𝟙 _) z).trans (appTop_id _)
  rw [← h, ← h, ← h, ofAdd_add, map_mul, Units.val_mul]

theorem existsUnique_pullback_charUnit [ConnectedSpace S]
    (f : splitTorus S X' ⟶ splitTorus S X) [IsMonHom f] (χ : X) :
    ∃! x : X', f.left.appTop.hom (charUnit S X χ).val = (charUnit S X' x).val := by
  haveI : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  obtain ⟨x, hx, hu⟩ := existsUnique_character_of_mul S X' (𝟙_ (Over S))
    (splitTorusPointsEquiv S X _ (fst (splitTorus S X') (𝟙_ (Over S)) ≫ f)
      (Multiplicative.ofAdd χ)) (fun Z t t' y => by
        rw [splitTorusPointsEquiv_val, ← appTop_comp, ← appTop_comp, ← appTop_comp,
          lift_fst_assoc, lift_fst_assoc, lift_fst_assoc, MonObj.mul_comp, appTop_mul_charUnit])
  refine ⟨x, ?_, fun x' hx' => hu x' ?_⟩
  · have := congrArg (lift (𝟙 (splitTorus S X')) (toUnit _)).left.appTop.hom hx
    rwa [splitTorusPointsEquiv_val, ← appTop_comp, ← appTop_comp, lift_fst_assoc, lift_fst,
      Category.id_comp, appTop_id] at this
  · beta_reduce at hx' ⊢
    rw [splitTorusPointsEquiv_val, appTop_comp, hx']

theorem charUnit_injective [ConnectedSpace S] {x y : X}
    (h : (charUnit S X x).val = (charUnit S X y).val) : x = y :=
  (existsUnique_pullback_charUnit (𝟙 (splitTorus S X)) x).unique (appTop_id _)
    ((appTop_id _).trans h)

theorem exists_addMonoidHom [ConnectedSpace S]
    (f : splitTorus S X' ⟶ splitTorus S X) [IsMonHom f] :
    ∃ φ : X →+ X', ∀ χ, f.left.appTop.hom (charUnit S X χ).val = (charUnit S X' (φ χ)).val := by
  choose c hc using fun χ => (existsUnique_pullback_charUnit f χ).exists
  refine ⟨AddMonoidHom.mk' c fun a b => charUnit_injective (S := S) ?_, hc⟩
  rw [← hc, charUnit_add, charUnit_add, map_mul, hc, hc]

end SplitTorusHom

open SplitTorusHom in

theorem exists_addEquiv_of_splitTorus_iso :
    ∀ (S : Scheme.{0}) [ConnectedSpace S] (X X' : Type) [AddCommGroup X] [AddCommGroup X']
      (θ : splitTorus S X' ≅ splitTorus S X), IsMonHom θ.hom →
      ∃ xe : X' ≃+ X, ∀ x : X',
        θ.hom.left.appTop.hom (charUnit S X (xe x)).val = (charUnit S X' x).val := by
  intro S _ X X' _ _ θ hθ
  obtain ⟨φ, hφ⟩ := exists_addMonoidHom θ.hom
  obtain ⟨ψ, hψ⟩ := exists_addMonoidHom θ.inv
  have h1 (x : X') : φ (ψ x) = x := charUnit_injective (S := S) (by
    rw [← hφ, ← hψ, ← appTop_comp, Iso.hom_inv_id, appTop_id])
  have h2 (x : X) : ψ (φ x) = x := charUnit_injective (S := S) (by
    rw [← hψ, ← hφ, ← appTop_comp, Iso.inv_hom_id, appTop_id])
  refine ⟨{ ψ with invFun := φ, left_inv := h1, right_inv := h2 }, fun x => ?_⟩
  rw [hφ]
  exact congrArg (fun z => (charUnit S X' z).val) (h1 x)

end GlobalTheory
