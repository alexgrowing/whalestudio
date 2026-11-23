import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GrpAlg

theorem inv_one_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (∀ (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G), x₀.left = x.left ≫ φ →
      (x₀⁻¹).left = (x⁻¹).left ≫ φ) ∧
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let F : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let Φ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) := MonoidHom.mk' F fun x y =>
    Over.OverMorphism.ext (h.2 T x y (F x) (F y) rfl rfl).symm
  refine ⟨fun x x₀ hx => ?_, congrArg (·.left) (map_one Φ).symm⟩
  obtain rfl : x₀ = Φ x := Over.OverMorphism.ext hx
  exact congrArg (·.left) (map_inv Φ x).symm

theorem exists_operation_of_extend {S : Scheme.{0}} {R : ℕ → Scheme.{0}} (s : ∀ e, R e ⟶ S)
    (r : ∀ e, R e ⟶ R (e + 1)) (Y : ∀ e, Over (R e)) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, β e ≫ (Y (e + 1)).hom = (Y e).hom ≫ r e)
    (B : Over S) (b : ∀ e, (Y e).left ⟶ B.left) (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (s e))
    (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    (W : Over S) (Z : ∀ e, Over (R e)) (w : ∀ e, (Z e).left ⟶ W.left)
    (hw : ∀ e, IsPullback (w e) (Z e).hom W.hom (s e)) (ζ : ∀ e, (Z e).left ⟶ (Z (e + 1)).left)
    (hζ : ∀ e, ζ e ≫ (Z (e + 1)).hom = (Z e).hom ≫ r e) (hζw : ∀ e, ζ e ≫ w (e + 1) = w e)
    (ext : ∀ f : ∀ e, (Z e).left ⟶ B.left, (∀ e, f e ≫ B.hom = w e ≫ W.hom) →
      (∀ e, ζ e ≫ f (e + 1) = f e) → ∃ g : W ⟶ B, ∀ e, w e ≫ g.left = f e)
    (J : Type) (p : J → (W ⟶ B)) (op : ∀ e (T : Over (R e)), (J → (T ⟶ Y e)) → (T ⟶ Y e))
    (nat : ∀ e T T' (t : T' ⟶ T) (x : J → (T ⟶ Y e)), t ≫ op e T x = op e T' fun i => t ≫ x i)
    (cmp : ∀ e (T : Over (R e)) (x : J → (T ⟶ Y e)) (x₀ : J → (Over.mk (T.hom ≫ r e) ⟶ Y (e + 1))),
      (∀ i, (x₀ i).left = (x i).left ≫ β e) → (op (e + 1) _ x₀).left = (op e T x).left ≫ β e) :
    ∃ g : W ⟶ B, ∀ e (T : Over (R e)) (x : J → (T ⟶ Y e)) (t : Over.mk (T.hom ≫ s e) ⟶ W),
      (∀ i, (t ≫ p i).left = (x i).left ≫ b e) → (t ≫ g).left = (op e T x).left ≫ b e := by
  have hp : ∀ e i, (w e ≫ (p i).left) ≫ B.hom = (Z e).hom ≫ s e :=
    fun e i => by rw [Category.assoc, Over.w (p i), (hw e).w]
  obtain ⟨X, hX⟩ : ∃ X : ∀ e, J → (Z e ⟶ Y e), ∀ e i, (X e i).left ≫ b e = w e ≫ (p i).left :=
    ⟨fun e i => Over.homMk ((hb e).lift _ _ (hp e i)) ((hb e).lift_snd _ _ _),
      fun e i => (hb e).lift_fst _ _ (hp e i)⟩
  obtain ⟨g, hg⟩ := ext (fun e => (op e _ (X e)).left ≫ b e)
    (fun e => by rw [Category.assoc, (hb e).w, ← Category.assoc, Over.w (op e _ (X e)), (hw e).w])
    (fun e => by
      obtain ⟨tr, h₁⟩ : ∃ tr : Over.mk ((Z e).hom ≫ r e) ⟶ Z (e + 1), tr.left = ζ e :=
        ⟨Over.homMk (ζ e) (hζ e), rfl⟩
      have h₂ := cmp e _ (X e) (fun i => tr ≫ X (e + 1) i) fun i => by
        apply (hb (e + 1)).hom_ext
        · rw [Over.comp_left, Category.assoc, Category.assoc, hX, hβb, hX, ← Category.assoc, h₁]
          exact congrArg (· ≫ (p i).left) (hζw e)
        · rw [Over.w, Category.assoc, hβ, ← Category.assoc, Over.w (X e i)]
          rfl
      rw [← nat, Over.comp_left, h₁] at h₂
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ b (e + 1)) h₂).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (hβb e)))))
  refine ⟨g, fun e T x t ht => ?_⟩
  obtain ⟨t', h₁⟩ : ∃ t' : T ⟶ Z e, t'.left ≫ w e = t.left :=
    ⟨Over.homMk ((hw e).lift t.left T.hom (Over.w t)) ((hw e).lift_snd _ _ _),
      (hw e).lift_fst _ _ (Over.w t)⟩
  have h₂ : x = fun i => t' ≫ X e i := funext fun i => Over.OverMorphism.ext <| by
    apply (hb e).hom_ext
    · rw [← ht, Over.comp_left, Over.comp_left, Category.assoc, hX, ← Category.assoc, h₁]
    · rw [Over.w, Over.w]
  rw [h₂, ← nat, Over.comp_left, Over.comp_left, Category.assoc, ← hg e, ← Category.assoc, h₁]

theorem exists_group_operations_of_extend {S : Scheme.{0}} {R : ℕ → Scheme.{0}} (s : ∀ e, R e ⟶ S)
    (r : ∀ e, R e ⟶ R (e + 1)) (Y : ∀ e, Over (R e)) [∀ e, GrpObj (Y e)]
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsGrpPullback (Y e) (Y (e + 1)) (r e) (β e))
    (B : Over S) (b : ∀ e, (Y e).left ⟶ B.left) (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (s e))
    (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    (Z : Over S → ∀ e, Over (R e)) (w : ∀ W e, (Z W e).left ⟶ W.left)
    (hw : ∀ W e, IsPullback (w W e) (Z W e).hom W.hom (s e))
    (ζ : ∀ W e, (Z W e).left ⟶ (Z W (e + 1)).left)
    (hζ : ∀ W e, ζ W e ≫ (Z W (e + 1)).hom = (Z W e).hom ≫ r e)
    (hζw : ∀ W e, ζ W e ≫ w W (e + 1) = w W e) (P : Over S → Prop)
    (ext : ∀ W, P W → ∀ f : ∀ e, (Z W e).left ⟶ B.left, (∀ e, f e ≫ B.hom = w W e ≫ W.hom) →
      (∀ e, ζ W e ≫ f (e + 1) = f e) → ∃ g : W ⟶ B, ∀ e, w W e ≫ g.left = f e)
    (h₂ : P (B ⊗ B)) (h₁ : P B) (h₀ : P (𝟙_ _)) :
    ∃ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (R e)) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ s e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ s e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) := by
  have key := fun W hW => exists_operation_of_extend s r Y β (fun e => (hβ e).1.w) B b hb hβb W (Z W) (w W)
    (hw W) (ζ W) (hζ W) (hζw W) (ext W hW)
  obtain ⟨mu, hmu⟩ := key _ h₂ Bool (fun i => cond i (fst B B) (snd B B))
    (fun _ _ x => x true * x false) (fun _ _ _ t x => comp_mul _ _ _)
    (fun e T x x₀ h => (hβ e).2 T _ _ _ _ (h true) (h false))
  obtain ⟨io, hio⟩ := key _ h₁ Unit (fun _ => 𝟙 B) (fun _ _ x => (x ())⁻¹)
    (fun _ _ _ t x => GrpObj.comp_inv _ _)
    (fun e T x x₀ h => (inv_one_of_isGrpPullback (hβ e) T).1 _ _ (h ()))
  obtain ⟨un, hun⟩ := key _ h₀ Empty Empty.elim (fun _ _ _ => 1) (fun _ _ _ t x => comp_one _)
    (fun e T x x₀ h => (inv_one_of_isGrpPullback (hβ e) T).2)
  refine ⟨mu, io, un, fun e T x y x₀ y₀ hx hy => ⟨?_, ?_, ?_⟩⟩
  · refine hmu e T (fun i => cond i x y) _ fun i => ?_
    cases i
    · exact (congrArg (·.left) (lift_snd x₀ y₀)).trans hy
    · exact (congrArg (·.left) (lift_fst x₀ y₀)).trans hx
  · exact hio e T (fun _ => x) _ fun _ => (congrArg (·.left) (Category.comp_id x₀)).trans hx
  · exact hun e T Empty.elim _ fun i => i.elim

theorem isPullback_fstG {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (W : Over (Spec (CommRingCat.of R))) :
    IsPullback (P := (thickObj R I e W).left) (fstG I e W).left (thickObj R I e W).hom W.hom (thick R I e) :=
  IsPullback.of_hasPullback W.hom (thick R I e)

theorem thickMap_hom {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (W : Over (Spec (CommRingCat.of R))) :
    thickMap R I e W ≫ (thickObj R I (e + 1) W).hom = (thickObj R I e W).hom ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

theorem thickMap_proj {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (W : Over (Spec (CommRingCat.of R))) :
    thickMap R I e W ≫ (fstG I (e + 1) W).left = (fstG I e W).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end GlobalTheory.GrpAlg

theorem GlobalTheory.GrpAlg.exists_group_operations : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ thick V (IsLocalRing.maximalIdeal V) e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) := by
  intro V _ _ _ _ Y _ β hβ B b hB hfl hb hβb
  have hfl₂ : Flat (B ⊗ B).hom := by
    change Flat (pullback.fst B.hom B.hom ≫ B.hom)
    infer_instance
  exact GlobalTheory.GrpAlg.exists_group_operations_of_extend (S := Spec (CommRingCat.of V))
    (R := fun e => Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))
    (thick V (IsLocalRing.maximalIdeal V)) (thickTrans V (IsLocalRing.maximalIdeal V)) Y β hβ B b hb hβb
    (fun W e => thickObj V (IsLocalRing.maximalIdeal V) e W)
    (fun W e => (fstG (IsLocalRing.maximalIdeal V) e W).left)
    (fun W e => GlobalTheory.GrpAlg.isPullback_fstG _ e W) (fun W e => thickMap V (IsLocalRing.maximalIdeal V) e W)
    (fun W e => GlobalTheory.GrpAlg.thickMap_hom _ e W) (fun W e => GlobalTheory.GrpAlg.thickMap_proj _ e W)
    (fun W => IsProjBy W.hom ∧ Flat W.hom) (fun W hW => GlobalTheory.MorAlg.exists_hom_of_thickenings V W B hW.1 hB hW.2)
    ⟨isProjBy_tensor V B B hB hB, hfl₂⟩ ⟨hB, hfl⟩
    ⟨isProjBy_id V, inferInstanceAs (Flat (𝟙 (Spec (CommRingCat.of V))))⟩
