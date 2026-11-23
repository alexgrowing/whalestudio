import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CmAugCocycle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FFible
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FRiCalc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FibInit

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

section gam

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

theorem gam_h {E : Type u''} [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C)
    {x y : Comma ι j} (φ : x ⟶ y) (a : F.obj (ι.obj x.left)) :
    (F.map y.hom).hom ((F.map (ι.map φ.left)).hom a) = (F.map (j.map φ.right)).hom ((F.map x.hom).hom a) := by
  rw [← ModuleCat.comp_apply, ← F.map_comp, ← ModuleCat.comp_apply, ← F.map_comp, φ.w]

def gamCm {E : Type u''} [Category.{v''} E] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) (ι : E ⥤ C) :
    Mor (ι ⋙ F) (Comma.snd ι j ⋙ j ⋙ F) (RingHom.id R) :=
  ⟨Comma.fst ι j, fun x => (F.map x.hom).hom, fun φ a => gam_h F j ι φ a⟩

structure GamDat {Γ : Type} [CommMonoid Γ] {D : C} (γ : Γ →* End D) (j : C' ⥤ C) (t : C') where
  S : C
  il : D ⟶ S
  ir : j.obj t ⟶ S
  g : Γ →* End S
  hil : ∀ a, il ≫ (g a : S ⟶ S) = (γ a : D ⟶ D) ≫ il
  hir : ∀ a, ir ≫ (g a : S ⟶ S) = ir
  hu : ∀ (t' : C') (c : D ⟶ j.obj t') (φ : j.obj t ⟶ j.obj t'), ∃! ψ : S ⟶ j.obj t', il ≫ ψ = c ∧ ir ≫ ψ = φ

namespace GamDat

variable {Γ : Type} [CommMonoid Γ] {D : C} {γ : Γ →* End D} {j : C' ⥤ C} {t : C'} (P : GamDat γ j t)

theorem uniq {t' : C'} (ψ ψ' : P.S ⟶ j.obj t') (h1 : P.il ≫ ψ = P.il ≫ ψ') (h2 : P.ir ≫ ψ = P.ir ≫ ψ') : ψ = ψ' :=
  (P.hu t' _ _).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩

noncomputable def ψ (x : StructuredArrow t (Comma.snd (SingleObj.functor γ) j)) : P.S ⟶ j.obj x.right.right :=
  (P.hu x.right.right x.right.hom (j.map x.hom)).exists.choose

theorem ψ_spec (x : StructuredArrow t (Comma.snd (SingleObj.functor γ) j)) :
    P.il ≫ P.ψ x = x.right.hom ∧ P.ir ≫ P.ψ x = j.map x.hom :=
  (P.hu x.right.right x.right.hom (j.map x.hom)).exists.choose_spec

theorem ψ_nat {x y : StructuredArrow t (Comma.snd (SingleObj.functor γ) j)} (f : x ⟶ y) :
    (P.g f.right.left : P.S ⟶ P.S) ≫ P.ψ y = P.ψ x ≫ j.map f.right.right := by
  have hw : (γ f.right.left : D ⟶ D) ≫ y.right.hom = x.right.hom ≫ j.map f.right.right := f.right.w
  have hw' : x.hom ≫ f.right.right = y.hom := StructuredArrow.w f
  apply P.uniq
  · rw [← Category.assoc, P.hil, Category.assoc, (P.ψ_spec y).1, ← Category.assoc, (P.ψ_spec x).1, hw]
  · rw [← Category.assoc, P.hir, (P.ψ_spec y).2, ← Category.assoc, (P.ψ_spec x).2, ← j.map_comp, hw']

noncomputable def μ (F : C ⥤ ModuleCat.{w} R) : Mor (SingleObj.functor P.g ⋙ F)
    (StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ (Comma.snd (SingleObj.functor γ) j ⋙ j ⋙ F))
    (RingHom.id R) where
  G := StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ Comma.fst (SingleObj.functor γ) j
  τ x := (F.map (P.ψ x)).hom
  nat {x y} f a := by
    show (F.map (P.ψ y)).hom ((F.map (P.g f.right.left : P.S ⟶ P.S)).hom a) =
      (F.map (j.map f.right.right)).hom ((F.map (P.ψ x)).hom a)
    rw [← ModuleCat.comp_apply, ← F.map_comp, ← ModuleCat.comp_apply, ← F.map_comp, P.ψ_nat]

noncomputable def Ψ [j.Full] [j.Faithful] :
    Comma (SingleObj.functor P.g) j ⥤ StructuredArrow t (Comma.snd (SingleObj.functor γ) j) where
  obj X := StructuredArrow.mk (Y := ({ left := X.left, right := X.right, hom := P.il ≫ X.hom } :
      Comma (SingleObj.functor γ) j)) (j.preimage (P.ir ≫ X.hom))
  map {X Y} f := StructuredArrow.homMk
    { left := f.left, right := f.right
      w := by
        have hw : (P.g f.left : P.S ⟶ P.S) ≫ Y.hom = X.hom ≫ j.map f.right := f.w
        show (γ f.left : D ⟶ D) ≫ P.il ≫ Y.hom = (P.il ≫ X.hom) ≫ j.map f.right
        rw [← Category.assoc, ← P.hil, Category.assoc, hw, Category.assoc] }
    (by
      have hw : (P.g f.left : P.S ⟶ P.S) ≫ Y.hom = X.hom ≫ j.map f.right := f.w
      apply j.map_injective
      show j.map (j.preimage (P.ir ≫ X.hom) ≫ f.right) = j.map (j.preimage (P.ir ≫ Y.hom))
      rw [j.map_comp, Functor.map_preimage, Functor.map_preimage, Category.assoc, ← hw, ← Category.assoc, P.hir])
  map_id X := StructuredArrow.hom_ext _ _ (CommaMorphism.ext rfl rfl)
  map_comp f g := StructuredArrow.hom_ext _ _ (CommaMorphism.ext rfl rfl)

theorem ψΨ [j.Full] [j.Faithful] (T : Comma (SingleObj.functor P.g) j) : P.ψ (P.Ψ.obj T) = T.hom := by
  apply P.uniq
  · rw [(P.ψ_spec _).1]; rfl
  · rw [(P.ψ_spec _).2]; exact j.map_preimage _

theorem Ψ_full [j.Full] [j.Faithful] : P.Ψ.Full where
  map_surjective {X Y} f := by
    have w1 : (γ f.right.left : D ⟶ D) ≫ (P.il ≫ Y.hom) = (P.il ≫ X.hom) ≫ j.map f.right.right := f.right.w
    have w2 : j.preimage (P.ir ≫ X.hom) ≫ f.right.right = j.preimage (P.ir ≫ Y.hom) := StructuredArrow.w f
    have w : (P.g f.right.left : P.S ⟶ P.S) ≫ Y.hom = X.hom ≫ j.map f.right.right := by
      apply P.uniq
      · rw [← Category.assoc, P.hil, Category.assoc, w1, Category.assoc]
      · rw [← Category.assoc, P.hir, ← Category.assoc, ← j.map_preimage (P.ir ≫ X.hom), ← j.map_comp, w2,
          j.map_preimage]
    exact ⟨{ left := f.right.left, right := f.right.right, w := w }, StructuredArrow.hom_ext _ _ (CommaMorphism.ext rfl rfl)⟩

theorem Ψ_faithful [j.Full] [j.Faithful] : P.Ψ.Faithful where
  map_injective {_ _} {_ _} h := CommaMorphism.ext (congrArg (fun f => f.right.left) h) (congrArg (fun f => f.right.right) h)

theorem Ψ_essSurj [j.Full] [j.Faithful] : P.Ψ.EssSurj where
  mem_essImage Y := by
    let X : Comma (SingleObj.functor P.g) j := { left := Y.right.left, right := Y.right.right, hom := P.ψ Y }
    refine ⟨X, ⟨StructuredArrow.isoMk (Comma.isoMk (Iso.refl _) (Iso.refl _) ?_) ?_⟩⟩
    · show (SingleObj.functor γ).map (𝟙 Y.right.left) ≫ Y.right.hom = (P.il ≫ P.ψ Y) ≫ j.map (𝟙 _)
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      exact (P.ψ_spec Y).1.symm
    · show j.preimage (P.ir ≫ P.ψ Y) ≫ 𝟙 _ = Y.hom
      rw [Category.comp_id, (P.ψ_spec Y).2, j.preimage_map]

theorem Ψ_equiv [j.Full] [j.Faithful] : P.Ψ.IsEquivalence := by
  have := P.Ψ_full
  have := P.Ψ_faithful
  have := P.Ψ_essSurj
  exact {}

theorem μ_iso [j.Full] [j.Faithful] (F : C ⥤ ModuleCat.{w} R) (s : R) (hD : Desc s F j) (n : ℕ) :
    IsoLe (1 * s ^ (2 * (n + 1) + 3)) (n + 1) (P.μ F) := by
  intro q hq
  have h1 : UpTo (s ^ (2 * (n + 1) + 3)) ((gamCm F j (SingleObj.functor P.g)).pull q) :=
    CrystallineSemistableComparison.B.P.comma1 F j (SingleObj.functor P.g) s (fun φ a => gam_h F j _ φ a) hD (n + 1) q hq
  have := P.Ψ_equiv
  let F' := StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ (Comma.snd (SingleObj.functor γ) j ⋙ j ⋙ F)
  have hb : UpTo (1 : R) ((Mor.restrict F' P.Ψ).pull q) :=
    ((CrystallineSemistableComparison.P.upTo_alg ((Mor.restrict F' P.Ψ).pull q) LinearMap.id (1 : R) 1).2.2.2.2).2
      (CrystallineSemistableComparison.P.adj F' P.Ψ _ P.Ψ.asEquivalence.toAdjunction q)
  let η : Comma.fst (SingleObj.functor P.g) j ⟶
      P.Ψ ⋙ (StructuredArrow.proj t (Comma.snd (SingleObj.functor γ) j) ⋙ Comma.fst (SingleObj.functor γ) j) :=
    { app := fun X => 𝟙 X.left
      naturality := fun X Y f => by
        show f.left ≫ 𝟙 Y.left = 𝟙 X.left ≫ f.left
        rw [Category.comp_id, Category.id_comp] }
  have heq : (Mor.restrict F' P.Ψ).pull q ∘ₗ (P.μ F).pull q = (gamCm F j (SingleObj.functor P.g)).pull q := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, ← (CrystallineSemistableComparison.P.pull_comp (P.μ F) (Mor.restrict F' P.Ψ) q x).1]
    refine (CrystallineSemistableComparison.P.prism (gamCm F j (SingleObj.functor P.g)) ((P.μ F).comp (Mor.restrict F' P.Ψ)) η ?_ q x).symm
    intro T a
    show (F.map (P.ψ (P.Ψ.obj T))).hom ((F.map ((SingleObj.functor P.g).map (𝟙 T.left))).hom a) = (F.map T.hom).hom a
    rw [CategoryTheory.Functor.map_id, F.map_id, ModuleCat.id_apply, P.ψΨ]
    rfl
  rw [← heq] at h1
  exact (CrystallineSemistableComparison.P.upTo_alg ((P.μ F).pull q) ((Mor.restrict F' P.Ψ).pull q) (1 : R) _).2.2.1 hb h1

end GamDat

end gam

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.gam : ∀ n : ℕ, ∃ N : ℕ, ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (j : C' ⥤ C) [j.Full] [j.Faithful] (Γ : Type) [CommMonoid Γ] (D : C) (γ : Γ →* End D) (s : R), Desc s F j → (∀ t : C', ∃ (S : C) (il : D ⟶ S) (ir : j.obj t ⟶ S) (g : Γ →* End S), (∀ a, il ≫ (g a : S ⟶ S) = (γ a : D ⟶ D) ≫ il) ∧ (∀ a, ir ≫ (g a : S ⟶ S) = ir) ∧ (∀ (t' : C') (c : D ⟶ j.obj t') (φ : j.obj t ⟶ j.obj t'), ∃! ψ : S ⟶ j.obj t', il ≫ ψ = c ∧ ir ≫ ψ = φ) ∧ InjUpTo s (aug (SingleObj.functor g ⋙ F) fun _ => (F.map ir).hom) ∧ ExactUpTo s (aug (SingleObj.functor g ⋙ F) fun _ => (F.map ir).hom) (d (SingleObj.functor g ⋙ F) 0) ∧ ∀ i ≤ n, ExactUpTo s (d (SingleObj.functor g ⋙ F) i) (d (SingleObj.functor g ⋙ F) (i + 1))) → RI (s ^ N) n F (SingleObj.functor γ) := by
  intro n
  refine ⟨(2 * n + 3) + ((2 * n + 3) + (2 * n + 6) * (2 * n + 3)), ?_⟩
  intro R _ C _ C' _ F j _ _ Γ _ D γ s hD hT q hq
  have hA : UpTo (s ^ (2 * n + 3)) ((gamCm F j (SingleObj.functor γ)).pull q) :=
    CrystallineSemistableComparison.B.P.comma1 F j (SingleObj.functor γ) s (fun φ a => gam_h F j _ φ a) hD n q hq
  have hC : UpTo (s ^ (2 * n + 3)) ((Mor.restrict F j).pull q) :=
    CrystallineSemistableComparison.B.P.fib (Mor.restrict F j) s (fun T => hD T) n q hq
  have hS : UpTo ((s * (1 * s ^ (2 * (n + 1) + 3))) ^ (2 * n + 3))
      ((Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)).pull q) := by
    refine CrystallineSemistableComparison.B.P.fible (Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)) (s * (1 * s ^ (2 * (n + 1) + 3))) n
      (fun t => ?_) q hq
    obtain ⟨S, il, ir, g, hil, hir, hu, hinj, hex0, hex⟩ := hT t
    let P : GamDat γ j t := ⟨S, il, ir, g, hil, hir, hu⟩
    refine ⟨SingleObj Γ, inferInstance, SingleObj.functor g ⋙ F, P.μ F, fun _ => (F.map ir).hom, s,
      1 * s ^ (2 * (n + 1) + 3), rfl, ?_, ?_, P.μ_iso F s hD n, hinj, hex0, hex⟩
    · intro x a
      show (F.map (P.ψ x)).hom ((F.map ir).hom a) = (F.map (j.map x.hom)).hom a
      rw [← ModuleCat.comp_apply, ← F.map_comp, (P.ψ_spec x).2]
      rfl
    · intro x y φ a
      show (F.map (g φ : S ⟶ S)).hom ((F.map ir).hom a) = (F.map ir).hom a
      rw [← ModuleCat.comp_apply, ← F.map_comp, hir]
  have heq : (gamCm F j (SingleObj.functor γ)).pull q ∘ₗ (Mor.restrict F (SingleObj.functor γ)).pull q =
      (Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)).pull q ∘ₗ (Mor.restrict F j).pull q := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      ← (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F (SingleObj.functor γ)) (gamCm F j (SingleObj.functor γ)) q x).1,
      ← (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F j) (Mor.restrict (j ⋙ F) (Comma.snd (SingleObj.functor γ) j)) q x).1]
    refine CrystallineSemistableComparison.P.prism _ _ (Comma.natTrans (SingleObj.functor γ) j) (fun T a => rfl) q x
  have h2 := (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).1 hC hS
  rw [← heq] at h2
  have h3 := (CrystallineSemistableComparison.P.upTo_alg _ _ _ _).2.2.1 hA h2
  have e : s ^ ((2 * n + 3) + ((2 * n + 3) + (2 * n + 6) * (2 * n + 3))) =
      s ^ (2 * n + 3) * (s ^ (2 * n + 3) * (s * (1 * s ^ (2 * (n + 1) + 3))) ^ (2 * n + 3)) := by ring
  rw [e]
  exact h3
