import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsUnivRingBc

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Corr

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : IsGrpPullback G' G f F) {k : Type} [Field k] (tk : Spec (CommRingCat.of k) ⟶ S') (g : Spec (CommRingCat.of k) ⟶ S)
  (hg : tk ≫ f = g)

abbrev viaT (X : Over (Spec (CommRingCat.of k))) : Over S' := Over.mk (X.hom ≫ tk)

def Rel {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) : Prop :=
  w.left ≫ F = v.left ≫ pullback.fst G.hom g

def liftT {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) : viaT tk Y ⟶ viaT tk X :=
  Over.homMk φ.left (by
    show φ.left ≫ X.hom ≫ tk = Y.hom ≫ tk
    rw [← Category.assoc, Over.w φ])

variable {tk g}

theorem one_left' {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [CategoryTheory.Hom.one_def, Over.comp_left]
  first | rfl | simp

theorem comp_one'' {T : Scheme.{0}} {X Y M : Over T} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  rw [CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, ← Category.assoc, comp_toUnit]

include hc in
theorem rel_uniq_w {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v) : w = w' := by
  apply Over.OverMorphism.ext
  exact hc.1.hom_ext (h.trans h'.symm) ((Over.w w).trans (Over.w w').symm)

theorem rel_uniq_v {X : Over (Spec (CommRingCat.of k))} {w : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w v') : v = v' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h.symm.trans h'
  · exact (Over.w v).trans (Over.w v').symm

include hc hg in
theorem rel_exists_w {X : Over (Spec (CommRingCat.of k))} (v : X ⟶ (Over.pullback g).obj G) :
    ∃ w : viaT tk X ⟶ G', Rel (F := F) tk g w v := by
  have hv : v.left ≫ pullback.snd G.hom g = X.hom := Over.w v
  refine ⟨Over.homMk (hc.1.lift (v.left ≫ pullback.fst G.hom g) (X.hom ≫ tk) ?_) ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hv, Category.assoc, hg]
  · exact hc.1.lift_snd _ _ _
  · exact hc.1.lift_fst _ _ _

include hc hg in
theorem rel_exists_v {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') :
    ∃ v : X ⟶ (Over.pullback g).obj G, Rel (F := F) tk g w v := by
  have hw : w.left ≫ G'.hom = X.hom ≫ tk := Over.w w
  refine ⟨Over.homMk (pullback.lift (w.left ≫ F) X.hom ?_) ?_, ?_⟩
  · rw [Category.assoc, hc.1.w, ← Category.assoc, hw, Category.assoc, hg]
  · exact pullback.lift_snd _ _ _
  · exact (pullback.lift_fst _ _ _).symm

def iota2 (hg : tk ≫ f = g) (X : Over (Spec (CommRingCat.of k))) :
    Over.mk (X.hom ≫ g) ⟶ Over.mk ((viaT tk X).hom ≫ f) :=
  Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (X.hom ≫ tk) ≫ f = X.hom ≫ g
    rw [Category.id_comp, Category.assoc, hg])

theorem rel_iff {X : Over (Spec (CommRingCat.of k))} (w : viaT tk X ⟶ G') (v : X ⟶ (Over.pullback g).obj G) :
    Rel (F := F) tk g w v ↔
      pushPt (isGrpPullback_pullback G g).1.w v = iota2 hg X ≫ pushPt hc.1.w w := by
  constructor
  · intro h
    apply Over.OverMorphism.ext
    show v.left ≫ pullback.fst G.hom g = 𝟙 _ ≫ w.left ≫ F
    rw [Category.id_comp]
    exact h.symm
  · intro h
    have h2 : v.left ≫ pullback.fst G.hom g = 𝟙 _ ≫ w.left ≫ F := congrArg (fun u => u.left) h
    rw [Category.id_comp] at h2
    exact h2.symm

include hc hg in
theorem rel_mul {X : Over (Spec (CommRingCat.of k))} {w w' : viaT tk X ⟶ G'} {v v' : X ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) (h' : Rel (F := F) tk g w' v') : Rel (F := F) tk g (w * w') (v * v') := by
  have e := (rel_iff hc hg w v).1 h
  have e' := (rel_iff hc hg w' v').1 h'
  have h1 := (isGrpPullback_pullback G g).2 X v v' (pushPt (isGrpPullback_pullback G g).1.w v)
    (pushPt (isGrpPullback_pullback G g).1.w v') rfl rfl
  have h2 := hc.2 (viaT tk X) w w' (pushPt hc.1.w w) (pushPt hc.1.w w') rfl rfl
  show (w * w').left ≫ F = (v * v').left ≫ pullback.fst G.hom g
  rw [← h1, ← h2, e, e', CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def, ← comp_lift,
    Category.assoc]
  exact (Category.id_comp _).symm

include hc hg in
theorem rel_one {X : Over (Spec (CommRingCat.of k))} : Rel (F := F) tk g (1 : viaT tk X ⟶ G') (1 : X ⟶ (Over.pullback g).obj G) := by
  have p1 : ∀ {T : Over S'} {T' : Over S} (e : T' ⟶ Over.mk (T.hom ≫ f)),
      e ≫ pushPt hc.1.w (1 : T ⟶ G') = 1 := by
    intro T T' e
    have hm := hc.2 T 1 1 (pushPt hc.1.w (1 : T ⟶ G')) (pushPt hc.1.w (1 : T ⟶ G')) rfl rfl
    rw [_root_.mul_one] at hm
    have hp : pushPt hc.1.w (1 : T ⟶ G') * pushPt hc.1.w (1 : T ⟶ G') = pushPt hc.1.w (1 : T ⟶ G') :=
      Over.OverMorphism.ext hm
    rw [mul_eq_left] at hp
    rw [hp, comp_one'']
  have p2 : pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) = 1 := by
    have hm := (isGrpPullback_pullback G g).2 X 1 1 (pushPt (isGrpPullback_pullback G g).1.w 1)
      (pushPt (isGrpPullback_pullback G g).1.w 1) rfl rfl
    rw [_root_.mul_one] at hm
    have hp : pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) *
        pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) =
        pushPt (isGrpPullback_pullback G g).1.w (1 : X ⟶ (Over.pullback g).obj G) :=
      Over.OverMorphism.ext hm
    rwa [mul_eq_left] at hp
  exact (rel_iff hc hg _ _).2 (p2.trans (p1 (iota2 hg X)).symm)

include hc hg in
theorem rel_prod : ∀ {N : ℕ} {X : Over (Spec (CommRingCat.of k))} (u : Fin N → (viaT tk X ⟶ G'))
    (u' : Fin N → (X ⟶ (Over.pullback g).obj G)), (∀ i, Rel (F := F) tk g (u i) (u' i)) →
    Rel (F := F) tk g (List.ofFn u).prod (List.ofFn u').prod
  | 0, X, u, u', _ => by simpa using rel_one hc hg (X := X)
  | N + 1, X, u, u', h => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    exact rel_mul hc hg (h 0) (rel_prod (fun i => u i.succ) (fun i => u' i.succ) fun i => h i.succ)

theorem rel_pre {X Y : Over (Spec (CommRingCat.of k))} (φ : Y ⟶ X) {w : viaT tk X ⟶ G'}
    {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) : Rel (F := F) tk g (liftT tk φ ≫ w) (φ ≫ v) := by
  unfold Rel at h ⊢
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, h]
  first | rfl | skip

theorem rel_act (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) {X : Over (Spec (CommRingCat.of k))}
    {w : viaT tk X ⟶ G'} {v : X ⟶ (Over.pullback g).obj G} (h : Rel (F := F) tk g w v) :
    Rel (F := F) tk g (w ≫ a) (v ≫ (Over.pullback g).map b) := by
  unfold Rel at h ⊢
  rw [Over.comp_left, Category.assoc, hab, ← Category.assoc, h, Over.comp_left, Category.assoc,
    Category.assoc]
  congr 1
  exact (pullback.lift_fst _ _ _).symm

end Corr

end ReciprocityTheory.ChartRestriction.G.Chart
