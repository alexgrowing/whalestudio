import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusTrivial

theorem exists_isPullback {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {T G B W V : C} [GrpObj T] [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : T ⟶ G)
    [IsMonHom q] [IsMonHom i] (hk : IsPullback i (toUnit _) q η[B])
    {j : W ⟶ G} {k : V ⟶ B} {q' : W ⟶ V} (hW : IsPullback j q' q k) [Mono j] (τ : W ⟶ T)
    (hτ : ∀ (Z : C) (t : Z ⟶ T) (g g' : Z ⟶ W), g' ≫ j = (t ≫ i) * (g ≫ j) →
      g' ≫ τ = t * (g ≫ τ)) :
    ∃ a : T ⊗ W ⟶ W, IsPullback (𝟙 _) a (T ◁ q') (lift τ q') := by
  have hiq : ∀ {Z : C} (t : Z ⟶ T), (t ≫ i) ≫ q = 1 := by
    intro Z t
    rw [Category.assoc, hk.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  let s : T ⊗ W ⟶ T := fst T W * (snd T W ≫ τ)⁻¹
  have hw : ((s ≫ i) * (snd T W ≫ j)) ≫ q = (snd T W ≫ q') ≫ k := by
    rw [MonObj.mul_comp, hiq, _root_.one_mul, Category.assoc, Category.assoc, hW.w]
  let a : T ⊗ W ⟶ W := hW.lift _ _ hw
  have ha₁ : a ≫ j = (s ≫ i) * (snd T W ≫ j) := hW.lift_fst _ _ _
  have ha₂ : a ≫ q' = snd T W ≫ q' := hW.lift_snd _ _ _
  have ha₃ : a ≫ τ = fst T W := by
    rw [hτ _ _ _ _ ha₁]
    simp [s]
  have hsq : 𝟙 _ ≫ T ◁ q' = a ≫ lift τ q' := by
    ext <;> simp [ha₂, ha₃]
  refine ⟨a, ⟨hsq⟩, ⟨PullbackCone.IsLimit.mk hsq (fun c => c.fst) (fun c => by simp)
    (fun c => ?_) (fun c m h _ => by simpa using h)⟩⟩
  have h₁ : c.fst ≫ fst T W = c.snd ≫ τ := by
    simpa using c.condition =≫ fst _ _
  have h₂ : c.fst ≫ snd T W ≫ q' = c.snd ≫ q' := by
    simpa using c.condition =≫ snd _ _
  have h₃ : ((c.snd ≫ j) * (c.fst ≫ snd T W ≫ j)⁻¹) ≫ q = toUnit _ ≫ η[B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, ← Hom.one_def]
    simp only [Category.assoc, hW.w]
    rw [reassoc_of% h₂, mul_inv_cancel]
  let r : c.pt ⟶ T := hk.lift _ _ h₃
  have hr : r ≫ i = (c.snd ≫ j) * (c.fst ≫ snd T W ≫ j)⁻¹ := hk.lift_fst _ _ _
  have h₄ : c.snd ≫ j = (r ≫ i) * ((c.fst ≫ snd T W) ≫ j) := by
    rw [hr]; simp
  have h₅ := hτ _ _ _ _ h₄
  have h₆ : c.fst ≫ s = r := by
    simp only [s, MonObj.comp_mul, GrpObj.comp_inv, h₁, h₅, Category.assoc, mul_inv_cancel_right]
  rw [← cancel_mono j, Category.assoc, ha₁, MonObj.comp_mul, reassoc_of% h₆, h₄, Category.assoc]

theorem isAffine_and_bijective {S : Scheme.{0}} {X : Type} [AddCommGroup X] {W V : Over S}
    [IsAffine V.left] (τ : W ⟶ splitTorus S X) (q : W ⟶ V) [IsIso (lift τ q)]
    {A : CommRingCat.{0}} (e : A ≅ Γ(V.left, ⊤)) (f : AddMonoidAlgebra A X →+* Γ(W.left, ⊤))
    (hf₁ : ∀ a : A, f (AddMonoidAlgebra.single 0 a) = q.left.appTop.hom (e.hom.hom a))
    (hf₂ : ∀ χ : X, f (AddMonoidAlgebra.single χ 1) = τ.left.appTop.hom (charUnit S X χ).val) :
    IsAffine W.left ∧ Function.Bijective f := by
  let R : CommRingCat.{0} := .of (AddMonoidAlgebra A X)
  let F : R ⟶ Γ(W.left, ⊤) := CommRingCat.ofHom f
  let φ : W.left ⟶ Spec R := W.left.toSpecΓ ≫ Spec.map F
  have hφ : (Scheme.ΓSpecIso R).inv ≫ φ.appTop = F := by
    rw [SplitTorusPoints.ΓSpecIso_inv_comp_specMap, Scheme.toSpecΓ_appTop, Iso.inv_hom_id,
      Category.comp_id]
  have hφ' : ∀ x, φ.appTop.hom ((Scheme.ΓSpecIso R).inv.hom x) = f x := fun x =>
    congrArg (fun g => g.hom x) hφ
  let c : A ⟶ R := CommRingCat.ofHom (AddMonoidAlgebra.singleZeroRingHom)
  let v : Spec R ⟶ V.left := Spec.map (e.inv ≫ c) ≫ V.left.isoSpec.inv
  have hv : e.hom ≫ v.appTop = c ≫ (Scheme.ΓSpecIso R).inv := by
    have : V.left.isoSpec.inv.appTop = (Scheme.ΓSpecIso _).inv := by
      rw [← cancel_epi (Scheme.ΓSpecIso Γ(V.left, ⊤)).hom, Iso.hom_inv_id,
        ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
      exact congrArg Scheme.Hom.appTop V.left.isoSpec.inv_hom_id
    rw [Scheme.Hom.comp_appTop, this, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Iso.hom_inv_id_assoc]
  have hv' : ∀ a : A, v.appTop.hom (e.hom.hom a) =
      (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single 0 a) := fun a =>
    congrArg (fun g => g.hom a) hv
  let P : Over S := Over.mk (v ≫ V.hom)
  let v' : P ⟶ V := Over.homMk v rfl
  let t : P ⟶ splitTorus S X := (splitTorusPointsEquiv S X P).symm
    ((Scheme.ΓSpecIso R).inv.hom.toMonoidHom.comp (AddMonoidAlgebra.of A X)).toHomUnits
  have ht : ∀ χ : X, t.left.appTop.hom (charUnit S X χ).val =
      (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single χ 1) := by
    intro χ
    rw [← splitTorusPointsEquiv_val, MulEquiv.apply_symm_apply]
    rfl
  have hφv : φ ≫ v = q.left := by
    apply ext_of_isAffine
    rw [← cancel_epi e.hom, Scheme.Hom.comp_appTop, reassoc_of% hv, hφ]
    ext a
    exact hf₁ a
  let φ' : W ⟶ P := Over.homMk φ (by
    change φ ≫ v ≫ V.hom = _
    rw [reassoc_of% hφv, Over.w])
  have h₁ : φ' ≫ v' = q := Over.OverMorphism.ext hφv
  have h₂ : φ' ≫ t = τ := by
    apply (splitTorusPointsEquiv S X W).injective
    ext χ
    change (splitTorusPointsEquiv S X W _ (Multiplicative.ofAdd χ)).val =
      (splitTorusPointsEquiv S X W _ (Multiplicative.ofAdd χ)).val
    rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, ← hf₂, ← hφ', ← ht]
    rfl
  let σ : P ⟶ W := lift t v' ≫ inv (lift τ q)
  have hσ : σ ≫ lift τ q = lift t v' := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hσ₁ : σ ≫ τ = t := by simpa using hσ =≫ fst _ _
  have hσ₂ : σ ≫ q = v' := by simpa using hσ =≫ snd _ _
  have h₃ : φ' ≫ σ = 𝟙 _ := by
    rw [← cancel_mono (lift τ q), Category.assoc, hσ, comp_lift, h₁, h₂, Category.id_comp]
  let σ' : Spec R ⟶ W.left := σ.left
  have h₄ : σ' ≫ φ = 𝟙 _ := by
    apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso R).inv, Scheme.Hom.comp_appTop, reassoc_of% hφ]
    ext1
    apply AddMonoidAlgebra.ringHom_ext
    · intro a
      change σ'.appTop.hom (f (AddMonoidAlgebra.single 0 a)) =
        (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single 0 a)
      rw [hf₁, ← hv']
      exact congrArg (fun g : P ⟶ V => g.left.appTop.hom (e.hom.hom a)) hσ₂
    · intro χ
      change σ'.appTop.hom (f (AddMonoidAlgebra.single χ 1)) =
        (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single χ 1)
      rw [hf₂, ← ht]
      exact congrArg (fun g : P ⟶ _ => g.left.appTop.hom (charUnit S X χ).val) hσ₁
  have : IsIso φ := ⟨σ', congrArg CommaMorphism.left h₃, h₄⟩
  refine ⟨.of_isIso φ, ?_⟩
  have : IsIso φ.appTop := inferInstanceAs (IsIso (φ.app ⊤))
  have : IsIso F := by rw [← hφ]; infer_instance
  exact ConcreteCategory.bijective_of_isIso F

theorem app_comp_topIso_inv {Y Z : Scheme.{0}} (f : Y ⟶ Z) (V : Z.Opens) :
    f.app V ≫ (f ⁻¹ᵁ V).topIso.inv = V.topIso.inv ≫ (f ∣_ V).appTop := by
  rw [Scheme.Hom.appTop, morphismRestrict_app', Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv,
    Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.map_appLE _ _ _).symm

theorem cover_of_isPullback {P Y Z W : Scheme.{0}} {a : P ⟶ Y} {b : P ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
    (h : IsPullback a b f g)
    (hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) f) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) b :=
  ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h hf.1.1,
    MorphismProperty.of_isPullback (P := @Flat) h hf.1.2⟩,
    MorphismProperty.of_isPullback (P := @QuasiCompact) h hf.2⟩

end TorusTrivial

open TorusTrivial in

theorem isAffineOpen_and_bijective_of_weight_units :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∀ (V : B.left.Opens), IsAffineOpen V → ∀ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, (∀ (χ : X) (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)), (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom (u (Multiplicative.ofAdd χ)).val = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom (u (Multiplicative.ofAdd χ)).val) → IsAffineOpen (q.left ⁻¹ᵁ V) ∧ Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom ((Units.coeHom _).comp u) (fun _ _ => Commute.all _ _)) := by
  intro S X _ G B _ _ q i _ _ hfl hsu hqc hk V hV u hu
  let U : G.left.Opens := q.left ⁻¹ᵁ V
  let W : Over S := Over.mk (U.ι ≫ G.hom)
  let V' : Over S := Over.mk (V.ι ≫ B.hom)
  let j : W ⟶ G := Over.homMk U.ι rfl
  let k : V' ⟶ B := Over.homMk V.ι rfl
  let q' : W ⟶ V' := Over.homMk (q.left ∣_ V) (by
    change (q.left ∣_ V) ≫ V.ι ≫ B.hom = U.ι ≫ G.hom
    rw [morphismRestrict_ι_assoc, Over.w])
  have hW₀ : IsPullback U.ι (q.left ∣_ V) q.left V.ι := (isPullback_morphismRestrict q.left V).flip
  have hW : IsPullback j q' q k :=
    IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext hW₀.w) hW₀
  have : Mono j.left := inferInstanceAs (Mono U.ι)
  have : Mono j := Over.mono_of_mono_left j
  let τ : W ⟶ splitTorus S X := (splitTorusPointsEquiv S X W).symm
    ((Units.map U.topIso.inv.hom.toMonoidHom).comp u)
  have hτ₀ : ∀ χ : X, τ.left.appTop.hom (charUnit S X χ).val =
      U.topIso.inv.hom (u (Multiplicative.ofAdd χ)).val := by
    intro χ
    rw [← splitTorusPointsEquiv_val, MulEquiv.apply_symm_apply]
    rfl
  have hle : ∀ {Z : Over S} (g : Z ⟶ W), ⊤ ≤ (g ≫ j).left ⁻¹ᵁ U := by
    intro Z g x _
    exact (g.left x).2
  have hτ₁ : ∀ {Z : Over S} (g : Z ⟶ W) (χ : X), (g ≫ τ).left.appTop.hom (charUnit S X χ).val =
      ((g ≫ j).left.appLE U ⊤ (hle g)).hom (u (Multiplicative.ofAdd χ)).val := by
    intro Z g χ
    let g' : Z.left ⟶ U := g.left
    have h : U.topIso.inv ≫ g'.appTop = (g' ≫ U.ι).appLE U ⊤ (hle g) := by
      rw [← Scheme.Hom.appLE_comp_appLE g' U.ι U ⊤ ⊤ (by simp) (by simp), Scheme.Hom.appTop,
        Scheme.Hom.app_eq_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
      rfl
    change g'.appTop.hom (τ.left.appTop.hom (charUnit S X χ).val) = _
    rw [hτ₀]
    exact congrArg (fun f => f.hom (u (Multiplicative.ofAdd χ)).val) h
  obtain ⟨a, ha⟩ := exists_isPullback q i hk hW τ (by
    intro Z t g g' hg
    apply (splitTorusPointsEquiv S X Z).injective
    rw [map_mul]
    ext χ
    change (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val =
      (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val *
      (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val
    rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, hτ₁, hτ₁,
      TorusInj.appLE_of_eq (congrArg Over.Hom.left hg)]
    exact hu χ Z t (g ≫ j) _ _)
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) q'.left :=
    cover_of_isPullback hW₀ ⟨⟨hsu, hfl⟩, hqc⟩
  have hT : IsPullback (snd (splitTorus S X) W) (splitTorus S X ◁ q') q'
      (snd (splitTorus S X) V') := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => lift (c.snd ≫ fst _ _) c.fst)
      (fun c => by simp) (fun c => ?_) (fun c m h₁ h₂ => ?_)⟩⟩
    · ext <;> simp [c.condition]
    · ext <;> simp [← h₁, ← h₂]
  have hQ' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
      (splitTorus S X ◁ q').left :=
    cover_of_isPullback (hT.map (Over.forget S)) hQ
  have : IsIso (lift τ q').left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := .isomorphisms Scheme.{0})
      (ha.map (Over.forget S)) hQ' (MorphismProperty.isomorphisms.infer_property _)
  have : IsIso ((Over.forget S).map (lift τ q')) := this
  have : IsIso (lift τ q') := isIso_of_reflects_iso _ (Over.forget S)
  have : IsAffine V'.left := hV
  obtain ⟨h₁, h₂⟩ := isAffine_and_bijective τ q' (A := Γ(B.left, V)) V.topIso.symm
    (U.topIso.inv.hom.comp (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom
      ((Units.coeHom _).comp u) (fun _ _ => Commute.all _ _)))
    (fun a => by
      refine Eq.trans ?_ (congrArg (fun f => f.hom a) (app_comp_topIso_inv q.left V))
      refine congrArg U.topIso.inv.hom ?_
      refine (AddMonoidAlgebra.liftNC_single _ _ 0 a).trans ?_
      exact (congrArg (_ * ·) (((Units.coeHom _).comp u).map_one)).trans (_root_.mul_one _))
    (fun χ => by
      rw [hτ₀]
      simp [AddMonoidAlgebra.liftNCRingHom])
  refine ⟨h₁, ?_⟩
  exact (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso U.topIso.inv) _).mp h₂

end GlobalTheory
