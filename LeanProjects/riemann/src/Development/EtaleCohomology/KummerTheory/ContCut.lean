import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ContCut

def Lim {J : Type} [SmallCategory J] {K : Type 1} [Category.{0} K] (G : K ⥤ AddCommGrpCat.{1}) {D : J ⥤ K} (c : Cocone D) :
    Prop :=
  (∀ x : G.obj c.pt, ∃ (j : J) (y : G.obj (D.obj j)), (G.map (c.ι.app j)).hom y = x) ∧
  ∀ (j : J) (y : G.obj (D.obj j)), (G.map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (G.map (D.map f)).hom y = 0

structure MVSeq {K : Type 1} [Category.{0} K] (X U V W : ℤ → K ⥤ AddCommGrpCat.{1}) where
  f : ∀ n, X n ⟶ U n
  g : ∀ n, X n ⟶ V n
  a : ∀ n, U n ⟶ W n
  b : ∀ n, V n ⟶ W n
  δ : ∀ n, W n ⟶ X (n + 1)
  comm : ∀ n, f n ≫ a n = g n ≫ b n
  exUV : ∀ n k u v, ((a n).app k).hom u = ((b n).app k).hom v → ∃ x, ((f n).app k).hom x = u ∧ ((g n).app k).hom x = v
  exX : ∀ n k x, ((f (n + 1)).app k).hom x = 0 → ((g (n + 1)).app k).hom x = 0 → ∃ w, ((δ n).app k).hom w = x
  exW : ∀ n k w, ((δ n).app k).hom w = 0 ↔ ∃ u v, w = ((a n).app k).hom u - ((b n).app k).hom v

def IsMV {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X) : Prop :=
  IsOpenImmersion f ∧ IsOpenImmersion g ∧ IsPullback a b f g ∧ ∀ x : X, x ∈ Set.range f ∨ x ∈ Set.range g

def Hf {R : Type} [CommRing R] (F : Shv R) (n : ℤ) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} where
  obj X := AddCommGrpCat.of (H R (sch.obj X.unop) F n)
  map f := AddCommGrpCat.ofHom (pull R (sch.map f.unop) F n)
  map_id X := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => by
    change pull R (sch.map (𝟙 X.unop)) F n x = x
    rw [CategoryTheory.Functor.map_id, pull_id])
  map_comp f g := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => by
    change pull R (sch.map (g.unop ≫ f.unop)) F n x = pull R _ F n (pull R _ F n x)
    rw [Functor.map_comp, pull_comp])

theorem bcMap_comp {X : Scheme.{0}} {R A B C : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B) (k : R ⟶ C)
    (h : A ⟶ B) (h' : B ⟶ C) (e : f ≫ h = g) (e' : g ≫ h' = k) (e'' : f ≫ h ≫ h' = k) :
    bcMap p f k (h ≫ h') e'' = bcMap p g k h' e' ≫ bcMap p f g h e := by
  apply pullback.hom_ext <;> simp [bcMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

def bc {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R) : Under R ⥤ Scheme.{0}ᵒᵖ where
  obj A := op (pullback p (Spec.map A.hom))
  map {A B} h := (bcMap p A.hom B.hom h.right (Under.w h)).op
  map_id A := Quiver.Hom.unop_inj (by apply pullback.hom_ext <;> simp [bcMap])
  map_comp h h' := Quiver.Hom.unop_inj (bcMap_comp p _ _ _ h.right h'.right (Under.w h) (Under.w h') (Under.w (h ≫ h')))

def bcHom {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R) (e : f ≫ p = r)
    (s : R ⟶ A) : pullback r (Spec.map s) ⟶ pullback p (Spec.map s) :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by rw [Category.comp_id, e]) (by simp)

theorem bcHom_bcMap {U X : Scheme.{0}} {R A B : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) (t : R ⟶ B) (h : A ⟶ B) (e' : s ≫ h = t) :
    bcHom f p r e t ≫ bcMap p s t h e' = bcMap r s t h e' ≫ bcHom f p r e s := by
  apply pullback.hom_ext <;> simp [bcMap, bcHom, pullback.map, pullback.lift_fst, pullback.lift_snd,
    pullback.lift_snd_assoc, pullback.lift_fst_assoc]

def bcNat {U X : Scheme.{0}} {R : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R) (e : f ≫ p = r) :
    bc p ⟶ bc r where
  app A := (bcHom f p r e A.hom).op
  naturality _ _ h := Quiver.Hom.unop_inj (bcHom_bcMap f p r e _ _ h.right (Under.w h))

def Conn {R : Type} [CommRing R] (F : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (f : U ⟶ X) (g : V ⟶ X) (n : ℤ)
    (w : H R (sch.obj W) F n) (x : H R (sch.obj X) F (n + 1)) : Prop :=
  ∃ (s : Sec ((res R F).X n) U) (z : Sec ((res R F).X (n + 1)) X), IsCls w (Sec.res a s) ∧ IsCls x z ∧
    Sec.res f z = Sec.map ((res R F).d n (n + 1)) s ∧ Sec.res g z = 0

def Five : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] {K : Type 1} [Category.{0} K]
  (X U V W : ℤ → K ⥤ AddCommGrpCat.{1}), Nonempty (MVSeq X U V W) → ∀ {D : J ⥤ K} (c : Cocone D),
  (∀ n, Lim (U n) c) → (∀ n, Lim (V n) c) → (∀ n, Lim (W n) c) → ∀ n, Lim (X n) c

def Ind : Prop := ∀ (R : CommRingCat.{0}) (P : ∀ X : Scheme.{0}, (X ⟶ Spec R) → Prop),
  (∀ (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec R), P X p) →
  (∀ {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X) (p : X ⟶ Spec R), IsMV a b f g →
    P U (f ≫ p) → P V (g ≫ p) → P W (a ≫ f ≫ p) → P X p) →
  ∀ (X : Scheme.{0}) (p : X ⟶ Spec R) [QuasiCompact p] [IsSeparated p], P X p

def BC : Prop := ∀ {R A : CommRingCat.{0}} (s : R ⟶ A) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (p : X ⟶ Spec R) (pU : U ⟶ Spec R) (pV : V ⟶ Spec R) (pW : W ⟶ Spec R) (ea : a ≫ pU = pW) (eb : b ≫ pV = pW)
  (ef : f ≫ p = pU) (eg : g ≫ p = pV), IsMV a b f g →
  IsMV (bcHom a pU pW ea s) (bcHom b pV pW eb s) (bcHom f p pU ef s) (bcHom g p pV eg s)

def Glue : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X)
  (g : V ⟶ X), IsMV a b f g →
  (∀ z : Sec G X, Sec.res f z = 0 → Sec.res g z = 0 → z = 0) ∧
  ∀ (s : Sec G U) (t : Sec G V), Sec.res a s = Sec.res b t → ∃ z : Sec G X, Sec.res f z = s ∧ Sec.res g z = t

def Flasque : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) [Injective G] {W U : Scheme.{0}} (a : W ⟶ U) [Mono a],
  Function.Surjective fun s : Sec G U => Sec.res a s

def Delta : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X)
  (g : V ⟶ X), IsMV a b f g → ∀ n : ℤ, ∃ δ : H R (sch.obj W) F n →+ H R (sch.obj X) F (n + 1),
    ∀ w x, Conn F a f g n w x ↔ δ w = x

def Exact : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X)
  (g : V ⟶ X), IsMV a b f g → ∀ n : ℤ,
  (∀ u v, pull R (sch.map a) F n u = pull R (sch.map b) F n v →
    ∃ x, pull R (sch.map f) F n x = u ∧ pull R (sch.map g) F n x = v) ∧
  (∀ x, pull R (sch.map f) F (n + 1) x = 0 → pull R (sch.map g) F (n + 1) x = 0 → ∃ w, Conn F a f g n w x) ∧
  ∀ w, Conn F a f g n w 0 ↔ ∃ u v, w = pull R (sch.map a) F n u - pull R (sch.map b) F n v

def MVnat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K : Type 1} [Category.{0} K] (X U V W : K ⥤ Scheme.{0}ᵒᵖ)
  (f : X ⟶ U) (g : X ⟶ V) (a : U ⟶ W) (b : V ⟶ W),
  (∀ k, IsMV (a.app k).unop (b.app k).unop (f.app k).unop (g.app k).unop) →
  Nonempty (MVSeq (fun n => X ⋙ Hf F n) (fun n => U ⋙ Hf F n) (fun n => V ⋙ Hf F n) (fun n => W ⋙ Hf F n))

def AffRing : Prop := ∀ {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (p : X ⟶ Spec R),
  ∃ T : Under R ⥤ CommRingCat.{0}, Nonempty (bc p ≅ T ⋙ Scheme.Spec.rightOp) ∧ (∀ A, Nonempty (R ⟶ T.obj A)) ∧
    ∀ {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ Under R} (c : Cocone D),
      IsColimit ((Under.forget R).mapCocone c) → Nonempty (IsColimit (T.mapCocone c))

def Aff : Prop := B1 → ∀ (q : ℕ) {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (p : X ⟶ Spec R), IsUnit (q : R) →
  ∀ {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ Under R} (c : Cocone D),
    IsColimit ((Under.forget R).mapCocone c) → ∀ n i : ℤ, Lim (bc p ⋙ Hf (tw q i) n) c

theorem goal_of (h5 : Five) (hI : Ind) (hB : BC) (hM : MVnat) (hA : Aff) : Cont := by
  intro _ b1 q _ X R p _ _ hq J _ _ D c hc u hu v hv n i
  let D' : J ⥤ Under R :=
    { obj := fun j => Under.mk (u j)
      map := fun f => Under.homMk (D.map f) (hu f)
      map_id := fun j => by ext1; exact D.map_id j
      map_comp := fun f g => by ext1; exact D.map_comp f g }
  let c' : Cocone D' :=
    { pt := Under.mk v
      ι := { app := fun j => Under.homMk (c.ι.app j) (hv j)
             naturality := fun j k f => by ext1; exact c.ι.naturality f } }
  have hc' : IsColimit ((Under.forget R).mapCocone c') := hc
  have key : ∀ n, Lim (bc p ⋙ Hf (tw q i) n) c' := by
    refine hI R (fun X p => ∀ n, Lim (bc p ⋙ Hf (tw q i) n) c') (fun X _ p n => hA b1 q p hq c' hc' n i) ?_ X p
    intro W U V X a b f g p h hU hV hW
    have eb : b ≫ g ≫ p = a ≫ f ≫ p := by rw [← Category.assoc, ← h.2.2.1.w, Category.assoc]
    exact h5 _ _ _ _ (hM _ (tw q i) _ _ _ _ (bcNat f p _ rfl) (bcNat g p _ rfl) (bcNat a _ _ rfl) (bcNat b _ _ eb)
      fun k => hB k.hom a b f g p _ _ _ rfl eb rfl rfl h) c' hU hV hW
  exact key n

end LateralTheory.KummerTheory.ContCut

end
