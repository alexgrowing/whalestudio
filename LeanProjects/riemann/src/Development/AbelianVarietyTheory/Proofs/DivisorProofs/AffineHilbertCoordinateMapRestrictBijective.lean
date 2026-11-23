import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

theorem bijective_appLE_of_image_eq {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (V : X.Opens) (h : f ''ᵁ V = U) (e : V ≤ f ⁻¹ᵁ U) :
    Function.Bijective (f.appLE U V e).hom := by
  subst h
  have : f.appLE (f ''ᵁ V) V e = (f.appIso V).hom := (Scheme.Hom.appIso_hom' f V).symm
  rw [this]
  exact ConcreteCategory.bijective_of_isIso _

theorem appLE_congr_hom {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst h; rfl

theorem coord_restrict_bijective : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0})
    (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (U : Z.Opens) (W : U.toScheme.Opens),
    Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y (U.ι ''ᵁ W)) →
      Function.Bijective (GlobalTheory.HilbAff.coord A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) W) := by
  intro A B _ _ _ N r e σ Z y U W hb
  set a := U.ι with ha
  set y' := (functor A B r).map a.op y with hy'
  let f := bc A B y.1 a
  let J := y.2.1.comap f
  let φ : J.subscheme ⟶ y.2.1.subscheme := (y.2.1.comapIso f).hom ≫ pullback.snd f y.2.1.subschemeι
  have hbc_fst : f ≫ pullback.fst (str A B) y.1 = pullback.fst (str A B) (a ≫ y.1) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hbc_snd : f ≫ pullback.snd (str A B) y.1 = pullback.snd (str A B) (a ≫ y.1) ≫ a :=
    pullback.lift_snd _ _ _
  have hφι : φ ≫ y.2.1.subschemeι = J.subschemeι ≫ f := by
    simp only [φ, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have h1 : φ ≫ y.2.1.subschemeι ≫ pullback.fst _ y.1 = J.subschemeι ≫ pullback.fst _ (a ≫ y.1) := by
    rw [reassoc_of% hφι, hbc_fst]
  have h2 : φ ≫ y.2.1.subschemeι ≫ pullback.snd _ y.1 = (J.subschemeι ≫ pullback.snd _ (a ≫ y.1)) ≫ a := by
    rw [reassoc_of% hφι, hbc_snd, Category.assoc]
  have H : IsPullback (pullback.snd f y.2.1.subschemeι)
      (pullback.fst f y.2.1.subschemeι ≫ pullback.snd _ (a ≫ y.1))
      (y.2.1.subschemeι ≫ pullback.snd _ y.1) a :=
    (IsPullback.of_hasPullback f y.2.1.subschemeι).flip.paste_vert (isPullback_bc A B y.1 a)
  have hpb : IsPullback (J.subschemeι ≫ pullback.snd _ (a ≫ y.1)) φ a
      (y.2.1.subschemeι ≫ pullback.snd _ y.1) :=
    H.flip.of_iso (y.2.1.comapIso f).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← Category.assoc,
        Scheme.IdealSheafData.comapIso_inv_subschemeι])
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]; dsimp only [φ]; rw [Iso.inv_hom_id_assoc])
      (by simp) (by simp)
  haveI : IsOpenImmersion f :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_bc A B y.1 a).flip
      (inferInstanceAs (IsOpenImmersion U.ι))
  haveI : IsOpenImmersion φ := by dsimp only [φ]; infer_instance
  set X0 := a ''ᵁ W with hX0
  have hX : φ ''ᵁ ((subStr A B y') ⁻¹ᵁ W) = (subStr A B y) ⁻¹ᵁ X0 :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback hpb W
  have hle : (subStr A B y') ⁻¹ᵁ W ≤ φ ⁻¹ᵁ ((subStr A B y) ⁻¹ᵁ X0) := by
    rw [← hX]; exact (Scheme.Hom.preimage_image_eq φ _).ge
  have hW : W ≤ a ⁻¹ᵁ X0 := (Scheme.Hom.preimage_image_eq a W).ge
  let β := φ.appLE _ _ hle
  let α := a.appLE X0 W hW
  have hβ : Function.Bijective β.hom := bijective_appLE_of_image_eq φ _ _ hX hle
  have hα : Function.Bijective α.hom := bijective_appLE_of_image_eq a _ _ rfl hW
  have hAm : (subStr A B y).app X0 ≫ β = α ≫ (subStr A B y').app W := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((appLE_congr_hom h2 _ _ _ _).trans
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
  have hA : ∀ x, β.hom (algebraMap Γ(Z, X0) (Sec A B y X0) x) =
      algebraMap Γ(U.toScheme, W) (Sec A B y' W) (α.hom x) := by
    intro x
    change ((subStr A B y).app X0 ≫ β).hom x = (α ≫ (subStr A B y').app W).hom x
    rw [hAm]; rfl
  have hG : ∀ b, β.hom (gen A B y X0 b) = gen A B y' W b := by
    intro b
    change ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ _ _ ≫ β).hom _ =
      ((J.subschemeι ≫ pullback.fst _ (a ≫ y.1)).appLE ⊤ _ _).hom _
    have hGm : (y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ (subStr A B y ⁻¹ᵁ X0) (by simp) ≫ β =
        (J.subschemeι ≫ pullback.fst _ (a ≫ y.1)).appLE ⊤ (subStr A B y' ⁻¹ᵁ W) (by simp) :=
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_congr_hom h1 _ _ _ _)
    rw [hGm]; rfl
  have hc : ∀ c : Fin r → Γ(Z, X0), β.hom (coord A B e σ y X0 c) =
      coord A B e σ y' W (fun k => α.hom (c k)) := by
    intro c
    rw [coord, coord, Fintype.linearCombination_apply, Fintype.linearCombination_apply]
    simp only [Algebra.smul_def]
    erw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    erw [map_mul, hA, hG]
    rfl
  have hαe : Function.Bijective (fun c : Fin r → Γ(Z, X0) => fun k => α.hom (c k)) :=
    hα.comp_left
  have hcomp : (coord A B e σ y' W) ∘ (fun c : Fin r → Γ(Z, X0) => fun k => α.hom (c k)) =
      β.hom ∘ (coord A B e σ y X0) := by
    funext c; exact (hc c).symm
  rw [← Function.Bijective.of_comp_iff _ hαe, hcomp]
  exact hβ.comp hb

end GlobalTheory.HilbAff
