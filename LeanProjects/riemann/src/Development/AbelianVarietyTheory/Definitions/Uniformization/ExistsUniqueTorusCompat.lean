import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

def TorusCompat {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {X : Type} [AddCommGroup X] (f : S' ⟶ S)
    (F : G'.left ⟶ G.left) (i' : splitTorus S' X ⟶ G') (i : splitTorus S X ⟶ G) : Prop :=
  ∃ τ : (splitTorus S' X).left ⟶ (splitTorus S X).left, τ ≫ (splitTorus S X).hom = (splitTorus S' X).hom ≫ f ∧
    (∀ χ, τ.appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val) ∧ τ ≫ i.left = i'.left ≫ F

abbrev red {A : Type} [CommRing A] (J : Ideal A) : Spec (CommRingCat.of (A ⧸ J)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

section API

open SplitTorus (bcMap bcMap_hom)

variable {S S' S'' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem bcMap_charUnit (f : S' ⟶ S) (χ : X) :
    (bcMap f X).appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val := by
  rw [SplitTorus.charUnit_val, SplitTorus.charUnit_val, SplitTorus.bcMap_appTop_chi]

theorem splitTorus_left_hom_ext {Z : Scheme.{0}} (a b : Z ⟶ (splitTorus S X).left)
    (h : a ≫ (splitTorus S X).hom = b ≫ (splitTorus S X).hom)
    (hχ : ∀ χ, a.appTop.hom (charUnit S X χ).val = b.appTop.hom (charUnit S X χ).val) : a = b := by
  let a' : Over.mk (a ≫ (splitTorus S X).hom) ⟶ splitTorus S X := Over.homMk a
  let b' : Over.mk (a ≫ (splitTorus S X).hom) ⟶ splitTorus S X :=
    Over.homMk b (by simpa using h.symm)
  have hab : a' = b' := SplitTorus.hom_ext fun χ => by
    rw [SplitTorus.val_eq, SplitTorus.val_eq]
    have hc := hχ χ
    rw [SplitTorus.charUnit_val] at hc
    exact hc
  exact congrArg CommaMorphism.left hab

theorem eq_bcMap {f : S' ⟶ S} {τ : (splitTorus S' X).left ⟶ (splitTorus S X).left}
    (h : τ ≫ (splitTorus S X).hom = (splitTorus S' X).hom ≫ f)
    (hχ : ∀ χ, τ.appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val) : τ = bcMap f X :=
  splitTorus_left_hom_ext _ _ (by rw [h, bcMap_hom]) fun χ => by rw [hχ, bcMap_charUnit]

theorem bcMap_id : bcMap (𝟙 S) X = 𝟙 _ :=
  (eq_bcMap (τ := 𝟙 _) (by simp) fun χ => by simp).symm

theorem bcMap_comp (f' : S'' ⟶ S') (f : S' ⟶ S) :
    bcMap (f' ≫ f) X = bcMap f' X ≫ bcMap f X :=
  (eq_bcMap (τ := bcMap f' X ≫ bcMap f X)
    (by rw [Category.assoc, bcMap_hom, ← Category.assoc, bcMap_hom, Category.assoc]) fun χ => by
      show (bcMap f' X).appTop.hom ((bcMap f X).appTop.hom (charUnit S X χ).val) = _
      rw [bcMap_charUnit, bcMap_charUnit]).symm

variable {G'' : Over S''} {G' : Over S'} {G : Over S}

theorem torusCompat_iff {f : S' ⟶ S} {F : G'.left ⟶ G.left} {i' : splitTorus S' X ⟶ G'}
    {i : splitTorus S X ⟶ G} : TorusCompat f F i' i ↔ bcMap f X ≫ i.left = i'.left ≫ F := by
  constructor
  · rintro ⟨τ, h₁, h₂, h₃⟩
    rw [← eq_bcMap h₁ h₂]
    exact h₃
  · intro h
    exact ⟨bcMap f X, bcMap_hom f X, fun χ => bcMap_charUnit f χ, h⟩

theorem TorusCompat.refl (i : splitTorus S X ⟶ G) : TorusCompat (𝟙 S) (𝟙 G.left) i i := by
  rw [torusCompat_iff, bcMap_id, Category.id_comp, Category.comp_id]

theorem TorusCompat.trans {f' : S'' ⟶ S'} {f : S' ⟶ S} {F' : G''.left ⟶ G'.left}
    {F : G'.left ⟶ G.left} {i'' : splitTorus S'' X ⟶ G''} {i' : splitTorus S' X ⟶ G'}
    {i : splitTorus S X ⟶ G} (h' : TorusCompat f' F' i'' i') (h : TorusCompat f F i' i) :
    TorusCompat (f' ≫ f) (F' ≫ F) i'' i := by
  rw [torusCompat_iff] at h' h ⊢
  rw [bcMap_comp, Category.assoc, h, ← Category.assoc, h', Category.assoc]

theorem torusCompat_id_iff {i' i : splitTorus S X ⟶ G} :
    TorusCompat (𝟙 S) (𝟙 G.left) i' i ↔ i' = i := by
  rw [torusCompat_iff, bcMap_id, Category.id_comp, Category.comp_id]
  constructor
  · intro h
    exact Over.OverMorphism.ext h.symm
  · rintro rfl
    rfl

theorem TorusCompat.of_comp {H : Over S} (i : splitTorus S X ⟶ G) (φ : G ⟶ H) :
    TorusCompat (𝟙 S) φ.left i (i ≫ φ) := by
  rw [torusCompat_iff, bcMap_id, Category.id_comp, Over.comp_left]

theorem torusCompat_bcMap (f : S' ⟶ S) :
    TorusCompat f (bcMap f X) (𝟙 (splitTorus S' X)) (𝟙 (splitTorus S X)) := by
  rw [torusCompat_iff, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]

theorem existsUnique_torusCompat {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (hF : IsPullback F G'.hom G.hom f) (i : splitTorus S X ⟶ G) :
    ∃! i' : splitTorus S' X ⟶ G', TorusCompat f F i' i := by
  have hw : (bcMap f X ≫ i.left) ≫ G.hom = (splitTorus S' X).hom ≫ f := by
    rw [Category.assoc, Over.w i, bcMap_hom]
  refine ⟨Over.homMk (hF.lift _ _ hw) (hF.lift_snd _ _ hw), ?_, ?_⟩
  · dsimp only
    rw [torusCompat_iff]
    exact (hF.lift_fst _ _ hw).symm
  · intro j hj
    rw [torusCompat_iff] at hj
    ext
    apply hF.hom_ext
    · rw [← hj]
      simp
    · simp

theorem TorusCompat.unique {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (hF : IsPullback F G'.hom G.hom f) {i : splitTorus S X ⟶ G} {i₁ i₂ : splitTorus S' X ⟶ G'}
    (h₁ : TorusCompat f F i₁ i) (h₂ : TorusCompat f F i₂ i) : i₁ = i₂ :=
  (existsUnique_torusCompat hF i).unique h₁ h₂

theorem TorusCompat.of_comp_right {f' : S'' ⟶ S'} {f : S' ⟶ S} {F' : G''.left ⟶ G'.left}
    {F : G'.left ⟶ G.left} (hF : IsPullback F G'.hom G.hom f) (hF' : F' ≫ G'.hom = G''.hom ≫ f')
    {i'' : splitTorus S'' X ⟶ G''} {i' : splitTorus S' X ⟶ G'} {i : splitTorus S X ⟶ G}
    (h'' : TorusCompat (f' ≫ f) (F' ≫ F) i'' i) (h : TorusCompat f F i' i) :
    TorusCompat f' F' i'' i' := by
  rw [torusCompat_iff] at h'' h ⊢
  rw [bcMap_comp] at h''
  apply hF.hom_ext
  · simp only [Category.assoc] at h'' ⊢
    rw [← h, h'']
  · simp [hF', bcMap_hom]

private theorem torusCompat_mul_comp [GrpObj G'] [GrpObj G] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (hF : IsGrpPullback G' G f F) {i' : splitTorus S' X ⟶ G'} {i : splitTorus S X ⟶ G} [IsMonHom i]
    (h : TorusCompat f F i' i) {T : Over S'} (u v : T ⟶ splitTorus S' X) :
    (u * v) ≫ i' = (u ≫ i') * (v ≫ i') := by
  rw [torusCompat_iff] at h
  let p : Over.mk (T.hom ≫ f) ⟶ splitTorus S X :=
    Over.homMk (u.left ≫ bcMap f X) (by simp [bcMap_hom])
  let q : Over.mk (T.hom ≫ f) ⟶ splitTorus S X :=
    Over.homMk (v.left ≫ bcMap f X) (by simp [bcMap_hom])
  have hpq : (p * q).left = (u * v).left ≫ bcMap f X :=
    SplitTorus.mul_left_bcMap f X T u v p q rfl rfl
  have key : ((p ≫ i) * (q ≫ i)).left = ((u ≫ i') * (v ≫ i')).left ≫ F :=
    hF.2 T (u ≫ i') (v ≫ i') (p ≫ i) (q ≫ i)
      (by show (u.left ≫ bcMap f X) ≫ i.left = (u.left ≫ i'.left) ≫ F; rw [Category.assoc, h, Category.assoc])
      (by show (v.left ≫ bcMap f X) ≫ i.left = (v.left ≫ i'.left) ≫ F; rw [Category.assoc, h, Category.assoc])
  apply Over.OverMorphism.ext
  apply hF.1.hom_ext
  · calc ((u * v) ≫ i').left ≫ F = (u * v).left ≫ (i'.left ≫ F) := by simp
      _ = (u * v).left ≫ (bcMap f X ≫ i.left) := by rw [h]
      _ = (p * q).left ≫ i.left := by rw [hpq, Category.assoc]
      _ = ((p ≫ i) * (q ≫ i)).left := by rw [← MonObj.mul_comp]; rfl
      _ = _ := key
  · simp

theorem TorusCompat.isMonHom [GrpObj G'] [GrpObj G] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (hF : IsGrpPullback G' G f F) {i' : splitTorus S' X ⟶ G'} {i : splitTorus S X ⟶ G} [IsMonHom i]
    (h : TorusCompat f F i' i) : IsMonHom i' := by
  have hm : ∀ {T : Over S'} (u v : T ⟶ splitTorus S' X), (u * v) ≫ i' = (u ≫ i') * (v ≫ i') :=
    fun u v => torusCompat_mul_comp hF h u v
  have one_eq : ∀ (M : Over S') [MonObj M], (1 : 𝟙_ (Over S') ⟶ M) = η[M] := fun M _ => by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  constructor
  · have he := hm (1 : 𝟙_ (Over S') ⟶ splitTorus S' X) 1
    rw [_root_.mul_one] at he
    have h1 : (1 : 𝟙_ (Over S') ⟶ splitTorus S' X) ≫ i' = 1 := by simpa using he.symm
    rw [one_eq, one_eq] at h1
    exact h1
  · have hμ := hm (fst (splitTorus S' X) (splitTorus S' X)) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] at hμ
    exact hμ

end API

instance isClosedImmersion_red {A : Type} [CommRing A] (J : Ideal A) : IsClosedImmersion (red J) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem surjective_red {A : Type} [CommRing A] {J : Ideal A} (hJ : IsNilpotent J) :
    Surjective (red J) := by
  rw [surjective_iff]
  intro x
  have hx : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    obtain ⟨n, hn⟩ := hJ
    intro a ha
    have hpow : a ^ n ∈ J ^ n := Ideal.pow_mem_pow ha n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hpow
    exact x.isPrime.mem_of_pow_mem n (by rw [hpow]; exact zero_mem _)
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

example : TorusCompat (red (Ideal.span {(2 : ZMod 4)}))
    (SplitTorus.bcMap (red (Ideal.span {(2 : ZMod 4)})) ℤ) (𝟙 (splitTorus _ ℤ)) (𝟙 (splitTorus _ ℤ)) :=
  torusCompat_bcMap _

example (S : Scheme.{0}) (G : Over S) (i : splitTorus S ℤ ⟶ G) : TorusCompat (𝟙 S) (𝟙 _) i i :=
  TorusCompat.refl i

example : ¬ TorusCompat (𝟙 (Spec (CommRingCat.of ℚ))) (𝟙 _)
    (1 : splitTorus _ ℤ ⟶ splitTorus _ ℤ) (𝟙 (splitTorus _ ℤ)) := by
  rw [torusCompat_id_iff]
  intro h
  let S := Spec (CommRingCat.of ℚ)
  have hall : ∀ t : Over.mk (𝟙 S) ⟶ splitTorus S ℤ, t = 1 := fun t => by
    rw [← Category.comp_id t, ← h, MonObj.comp_one]
  let u : Γ(S, ⊤)ˣ := -1
  have h1 := SplitTorus.val_ofVal (T := Over.mk (𝟙 S)) (zmultiplesHom _ (Additive.ofMul u)) 1
  rw [hall (SplitTorus.ofVal _), SplitTorus.val_one] at h1
  have h2 : u = 1 := Units.ext (by simpa using h1.symm)
  have h3 := congrArg (fun v : Γ(S, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℚ)).hom.hom v.val) h2
  simp only [u, Units.val_neg, Units.val_one, map_neg, map_one] at h3
  norm_num at h3

end GlobalTheory.UU
end
