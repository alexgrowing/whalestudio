import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdicColimit

variable {R : Type} [CommRing R] (I : Ideal R)

abbrev thickι (e : ℕ) (T : Over (Spec (CommRingCat.of R))) : (thickObj R I e T).left ⟶ T.left :=
  pullback.fst T.hom (thick R I e)

abbrev thickHom (e : ℕ) {T' T : Over (Spec (CommRingCat.of R))} (r : T' ⟶ T) :
    (thickObj R I e T').left ⟶ (thickObj R I e T).left :=
  ((Over.pullback (thick R I e)).map r).left

def IsAdicColimit (T : Over (Spec (CommRingCat.of R))) : Prop :=
  ∀ (X : Scheme.{0}) (f : ∀ e : ℕ, (thickObj R I e T).left ⟶ X), (∀ e, thickMap R I e T ≫ f (e + 1) = f e) →
    ∃! g : T.left ⟶ X, ∀ e, thickι I e T ≫ g = f e

instance mono_thick (e : ℕ) : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

instance mono_thickι (e : ℕ) (T : Over (Spec (CommRingCat.of R))) : Mono (thickι I e T) :=
  inferInstanceAs (Mono (pullback.fst T.hom (thick R I e)))

@[reassoc]
theorem thickMap_ι (e : ℕ) (T : Over (Spec (CommRingCat.of R))) :
    thickMap R I e T ≫ thickι I (e + 1) T = thickι I e T :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem thickHom_ι (e : ℕ) {T' T : Over (Spec (CommRingCat.of R))} (r : T' ⟶ T) :
    thickHom I e r ≫ thickι I e T = thickι I e T' ≫ r.left :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem thickMap_thickHom (e : ℕ) {T' T : Over (Spec (CommRingCat.of R))} (r : T' ⟶ T) :
    thickMap R I e T' ≫ thickHom I (e + 1) r = thickHom I e r ≫ thickMap R I e T := by
  rw [← cancel_mono (thickι I (e + 1) T), Category.assoc, Category.assoc, thickHom_ι, thickMap_ι,
    thickMap_ι_assoc, thickHom_ι]

variable {I}

theorem IsAdicColimit.hom_ext {T : Over (Spec (CommRingCat.of R))} (h : IsAdicColimit I T) {X : Scheme.{0}}
    {g g' : T.left ⟶ X} (e : ∀ e, thickι I e T ≫ g = thickι I e T ≫ g') : g = g' :=
  (h X (fun e => thickι I e T ≫ g') fun e => thickMap_ι_assoc I e T g').unique e fun _ => rfl

theorem IsAdicColimit.of_iso {T' T : Over (Spec (CommRingCat.of R))} (r : T' ≅ T) (h : IsAdicColimit I T') :
    IsAdicColimit I T := by
  intro X f hf
  obtain ⟨g, hg, hu⟩ := h X (fun e => thickHom I e r.hom ≫ f e) fun e => by
    rw [thickMap_thickHom_assoc, hf]
  refine ⟨r.inv.left ≫ g, fun e => ?_, fun g' hg' => ?_⟩
  · rw [← thickHom_ι_assoc, hg, ← Over.comp_left_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  · rw [← hu (r.hom.left ≫ g') fun e => by rw [← thickHom_ι_assoc, hg'], ← Over.comp_left_assoc, Iso.inv_hom_id]
    exact (Category.id_comp _).symm

theorem isAdicColimit_of_factor {T : Over (Spec (CommRingCat.of R))} (n : ℕ)
    (σ : T.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))) (hσ : σ ≫ thick R I n = T.hom) : IsAdicColimit I T := by
  intro X f hf
  let s : T.left ⟶ (thickObj R I n T).left := pullback.lift (𝟙 _) σ ((Category.id_comp _).trans hσ.symm)
  have hs : s ≫ thickι I n T = 𝟙 _ := pullback.lift_fst _ _ _
  have key : ∀ (m k : ℕ) (W : Scheme.{0}) (a : W ⟶ (thickObj R I m T).left) (b : W ⟶ (thickObj R I (m + k) T).left),
      a ≫ thickι I m T = b ≫ thickι I (m + k) T → a ≫ f m = b ≫ f (m + k) := by
    intro m k
    induction k generalizing m with
    | zero => intro W a b h; rw [(cancel_mono _).1 h]; rfl
    | succ k ih =>
      intro W a b h
      have := ih (m + 1) W (a ≫ thickMap R I m T)
      rw [show m + 1 + k = m + (k + 1) by omega] at this
      rw [← this b (by rw [Category.assoc, thickMap_ι, h]), Category.assoc, hf]
  refine ⟨s ≫ f n, fun e => ?_, fun g hg => by rw [← hg n, reassoc_of% hs]⟩
  rw [← Category.assoc]
  rcases le_total e n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← key e k _ (𝟙 _) _ (by rw [Category.assoc, hs, Category.id_comp, Category.comp_id]), Category.id_comp]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [key n k _ _ (𝟙 _) (by rw [Category.assoc, hs, Category.id_comp, Category.comp_id]), Category.id_comp]

end GlobalTheory.AdicColimit
