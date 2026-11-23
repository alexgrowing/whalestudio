import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

section Hoc
variable {J : Type} [SmallCategory J]

def hocF (J : Type) [SmallCategory J] : (J ⥤ PSh) ⥤ Spc :=
  flipFunctor _ _ _ ⋙ (Functor.whiskeringRight _ _ _).obj (Functor.elementsFunctor ⋙ nerveFunctor) ⋙ flipFunctor _ _ _

abbrev hoc (D : J ⥤ PSh) : Spc := (hocF J).obj D

def chn {D : J ⥤ PSh} {n : SimplexCategoryᵒᵖ} {U : Scheme.{0}ᵒᵖ} (x : ((hoc D).obj n).obj U) :
    Fin (n.unop.len + 1) ⥤ (D.flip.obj U).Elements := x

def Coc (D : J ⥤ PSh) {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) : Prop := ∀ j k (f : j ⟶ k), D.map f ≫ c k = c j

def aug {D : J ⥤ PSh} {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c) : hoc D ⟶ disc.obj Y where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => (c ((chn x).obj 0).1).app U ((chn x).obj 0).2
      naturality := fun U U' f => by
        ext x
        exact ConcreteCategory.congr_hom ((c ((chn x).obj 0).1).naturality f) ((chn x).obj 0).2 }
  naturality n m θ := by
    ext U x
    have g := (chn x).map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (hc _ _ g.1) U) ((chn x).obj 0).2
    refine Eq.trans ?_ h
    exact congrArg (fun y => (c ((chn x).obj (θ.unop.toOrderHom 0)).1).app U y) g.2.symm

theorem map_aug {D' D : J ⥤ PSh} {Y : PSh} (α : D' ⟶ D) (c' : ∀ j, D'.obj j ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c')
    (hc : Coc D c) (h : ∀ j, α.app j ≫ c j = c' j) : (hocF J).map α ≫ aug c hc = aug c' hc' := by
  ext n U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h ((chn x).obj 0).1) U) ((chn x).obj 0).2

def mkChn {I : Type} [SmallCategory I] {F : J ⥤ Type} (σ : I ⥤ J) (s : ∀ i, F.obj (σ.obj i))
    (h : ∀ i k (g : i ⟶ k), F.map (σ.map g) (s i) = s k) : I ⥤ F.Elements where
  obj i := ⟨σ.obj i, s i⟩
  map g := ⟨σ.map g, h _ _ g⟩
  map_id i := Subtype.ext (σ.map_id i)
  map_comp g g' := Subtype.ext (σ.map_comp g g')

theorem mkChn_congr {I : Type} [SmallCategory I] {F : J ⥤ Type} (σ : I ⥤ J) {s s' : ∀ i, F.obj (σ.obj i)} (e : s = s') h h' :
    mkChn σ s h = mkChn σ s' h' := by subst e; rfl

theorem laurent_adjoin_eq_of_image_eq (D : J ⥤ PSh) {n : ℕ} (σ : Fin (n + 1) ⥤ J) (i k : Fin (n + 1)) (g : i ⟶ k) :
    D.map (σ.map (homOfLE (Fin.zero_le i))) ≫ D.map (σ.map g) = D.map (σ.map (homOfLE (Fin.zero_le k))) := by
  rw [← D.map_comp, ← σ.map_comp]; rfl

def inj (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) : D.obj (σ.obj 0) ⟶ (hoc D).obj n where
  app U := TypeCat.ofHom fun x => mkChn (F := D.flip.obj U) σ (fun i => (D.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)
    fun i k g => ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) x
  naturality U U' f := by
    ext x
    exact mkChn_congr (F := D.flip.obj U') σ
      (funext fun i => ConcreteCategory.congr_hom ((D.map (σ.map (homOfLE (Fin.zero_le i)))).naturality f) x)
      (fun i k g => ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U') _)
      (fun i k g => by
        have a := ConcreteCategory.congr_hom ((D.map (σ.map g)).naturality f) ((D.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)
        exact a.trans (congrArg ((D.obj (σ.obj k)).map f)
          (ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) x)))

end Hoc

def pbRel {B G E' E : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π') :
    pullback π' g ⟶ pullback π g := pullback.map π' g π g a (𝟙 _) (𝟙 _) (by simp [h]) (by simp)

def abvRel {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (a : E' ⟶ E) (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X)
    (h : a ≫ π = π') : abv U π' ⟶ abv U π :=
  Arrow.homMk (pbRel (sch.map U.ι) a π' π h) a (pullback.lift_fst _ _ _)

def Prd (q : ℕ) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {m j : ℤ} (c : Hs q (opn U) m j) : Prop :=
  ∀ n i : ℤ, Function.Bijective fun a : Ht q E n i => Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)

def Loc {X : Scheme.{0}} {E : Spc} (π : E ⟶ sch.obj X) : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (g : Y ⟶ X), QuasiIso ((chains R).map (pullback.snd π (sch.map g)))

def lev (n : SimplexCategoryᵒᵖ) : Arrow Spc ⥤ Arrow Spc := ((evaluation _ _).obj n ⋙ disc).mapArrow

def LeafLevel : Prop := ∀ (J : Type) [SmallCategory J] (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ),
  Nonempty (IsColimit (Cofan.mk ((hoc D).obj n) (inj D n)))

def LeafSum : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) (E : A → Spc) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ n : ℤ, Function.Bijective fun (x : H R c.pt F n) (a : A) => pull R (c.inj a) F n x

def LeafRel : Prop := ∀ (q : ℕ) (i : ℤ),
  ∃ e : ∀ (P : Arrow Spc) (n : ℤ), HK _ (cokernel ((chains (ZMod q)).map P.hom)) (tw q i) n ≃+ Hs q P n i,
    (∀ (P : Arrow Spc) (n : ℤ) (p : (chains (ZMod q)).obj (dbl P) ⟶ cokernel ((chains (ZMod q)).map P.hom)),
      (chains _).map (dbl.inl P) ≫ p = cokernel.π _ → (chains _).map (dbl.inr P) ≫ p = 0 →
      ∀ x, (e P n x).1 = HK.pull _ p (tw q i) n x)

def LeafExcLevel : Prop := A3 → ∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), (∀ n, Exc q ((lev n).map φ)) → Exc q φ

def LeafPrdLevel : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (U : X.Opens) (E : Spc) (π : E ⟶ sch.obj X) (m j : ℤ)
  (c : Hs q (opn U) m j), (∀ n, Prd q U (E := disc.obj (E.obj n)) (disc.map (π.app n)) c) → Prd q U π c

def LeafActNat : Prop := DivisorNaturality → ∀ (q : ℕ) [NeZero q] (P' P : Arrow Spc) (φ : P' ⟶ P) (n m i j : ℤ) (a : Ht q P.right n i)
  (b : Hs q P m j), Hs.pull q φ _ _ (Hs.act q a b) = Hs.act q (pull _ φ.right _ _ a) (Hs.pull q φ _ _ b)

def LeafHsSum : Prop := ∀ (q : ℕ) (X : Scheme.{0}) (U : X.Opens) (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ (π : c.pt ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X)
  (h : ∀ a, disc.map (c.inj a) ≫ disc.map π = disc.map (π' a)) (n i : ℤ),
  Function.Bijective fun (x : Hs q (abv U (E := disc.obj c.pt) (disc.map π)) n i) (a : A) =>
    Hs.pull q (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)) n i x

def LeafFstHoc : Prop := A3 → ∀ (R : Type) [CommRing R] (F : Shv R) (J : Type) [SmallCategory J] (D : J ⥤ PSh) (Y G : PSh)
  (g : G ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c), (∀ j, Eqv R (pullback.fst (disc.map (c j)) (disc.map g)) F) →
  Eqv R (pullback.fst (aug c hc) (disc.map g)) F

def LeafRelHoc : Prop := A3 → ∀ (R : Type) [CommRing R] (F : Shv R) (J : Type) [SmallCategory J] (D' D : J ⥤ PSh) (α : D' ⟶ D)
  (Y G : PSh) (g : G ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j)) h',
  (∀ j, Eqv R (pbRel (disc.map g) (disc.map (α.app j)) (disc.map (c' j)) (disc.map (c j)) (h j)) F) →
  Eqv R (pbRel (disc.map g) ((hocF J).map α) (aug c' hc') (aug c hc) h') F

def LeafExcHoc : Prop := A3 → ∀ (q : ℕ) (J : Type) [SmallCategory J] (D' D : J ⥤ PSh) (α : D' ⟶ D) (X : Scheme.{0})
  (U : X.Opens) (c' : ∀ j, D'.obj j ⟶ yoneda.obj X) (c : ∀ j, D.obj j ⟶ yoneda.obj X) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j)) h',
  (∀ j, Exc q (abvRel U (disc.map (α.app j)) (disc.map (c' j)) (disc.map (c j)) (h j))) →
  Exc q (abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h')

def LeafPrdHoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (J : Type) [SmallCategory J] (D : J ⥤ PSh) (X : Scheme.{0}) (U : X.Opens)
  (c : ∀ j, D.obj j ⟶ yoneda.obj X) (hc : Coc D c) (m k : ℤ) (b : Hs q (opn U) m k),
  (∀ j, Prd q U (E := disc.obj (D.obj j)) (disc.map (c j)) b) → Prd q U (aug c hc) b

def LeafLoc : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j), Loc (aug _ hc)

def LeafLocExc : Prop := A1 → ∀ (q : ℕ) (X : Scheme.{0}) (U : X.Opens) (E : Spc) (π : E ⟶ sch.obj X), Loc π → Exc q (abvMap U π)

def LeafPush : Prop := ∀ (J' J : Type) [SmallCategory J'] [SmallCategory J] (D' : J' ⥤ PSh) (D : J ⥤ PSh) (G : J' ⥤ J)
  (α : D' ⟶ G ⋙ D) (Y' Y : PSh) (f : Y' ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y') (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c),
  (∀ j, α.app j ≫ c (G.obj j) = c' j ≫ f) → ∃ b : hoc D' ⟶ hoc D, b ≫ aug c hc = aug c' hc' ≫ disc.map f

end LateralTheory.CohomologicalPurity.TubeCut
