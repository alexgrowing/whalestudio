import Development.EtaleCohomology.KummerTheory.ContCut

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.KummerTheory.FivePf
open LateralTheory.KummerTheory.ContCut

variable {K : Type 1} [Category.{0} K]

theorem mapc (G : K ⥤ AddCommGrpCat.{1}) {a b d : K} (f : a ⟶ b) (g : b ⟶ d) (x : G.obj a) :
    (G.map g).hom ((G.map f).hom x) = (G.map (f ≫ g)).hom x := by
  rw [G.map_comp]; rfl

theorem natap {F G : K ⥤ AddCommGrpCat.{1}} (α : F ⟶ G) {k k' : K} (h : k ⟶ k') (x : F.obj k) :
    (α.app k').hom ((F.map h).hom x) = (G.map h).hom ((α.app k).hom x) := by
  have := congrArg (fun φ => φ.hom x) (α.naturality h)
  exact this

theorem commap {X U V W : ℤ → K ⥤ AddCommGrpCat.{1}} (S : MVSeq X U V W) (n : ℤ) (k : K) (x : (X n).obj k) :
    ((S.a n).app k).hom (((S.f n).app k).hom x) = ((S.b n).app k).hom (((S.g n).app k).hom x) := by
  have := congrArg (fun φ => (φ.app k).hom x) (S.comm n)
  exact this

variable {J : Type} [SmallCategory J] {D : J ⥤ K}

theorem natι {F G : K ⥤ AddCommGrpCat.{1}} (α : F ⟶ G) (c : Cocone D) (j : J) (x : F.obj (D.obj j)) :
    (α.app c.pt).hom ((F.map (c.ι.app j)).hom x) = (G.map (c.ι.app j)).hom ((α.app (D.obj j)).hom x) :=
  natap α (c.ι.app j) x

theorem push (G : K ⥤ AddCommGrpCat.{1}) (c : Cocone D) {j k : J} (f : j ⟶ k) (y : G.obj (D.obj j)) :
    (G.map (c.ι.app k)).hom ((G.map (D.map f)).hom y) = (G.map (c.ι.app j)).hom y := by
  rw [mapc, c.w]

theorem five_succ [IsFiltered J] (X U V W : ℤ → K ⥤ AddCommGrpCat.{1}) (S : MVSeq X U V W) (c : Cocone D)
    (hU : ∀ n, Lim (U n) c) (hV : ∀ n, Lim (V n) c) (hW : ∀ n, Lim (W n) c) (m : ℤ) : Lim (X (m + 1)) c := by
  constructor
  · intro x
    obtain ⟨j1, u, hu⟩ := (hU (m + 1)).1 (((S.f (m + 1)).app c.pt).hom x)
    obtain ⟨j2, v, hv⟩ := (hV (m + 1)).1 (((S.g (m + 1)).app c.pt).hom x)
    obtain ⟨k, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs j1 j2
    have e0 : ((W (m + 1)).map (c.ι.app k)).hom
        (((S.a (m + 1)).app (D.obj k)).hom (((U (m + 1)).map (D.map g1)).hom u) -
          ((S.b (m + 1)).app (D.obj k)).hom (((V (m + 1)).map (D.map g2)).hom v)) = 0 := by
      rw [map_sub, ← natι (S.a (m + 1)), ← natι (S.b (m + 1)), push, push, hu, hv, commap, sub_self]
    obtain ⟨k2, f2, h2⟩ := (hW (m + 1)).2 k _ e0
    rw [map_sub, ← natap (S.a (m + 1)), ← natap (S.b (m + 1)), sub_eq_zero] at h2
    obtain ⟨x', hx1, hx2⟩ := S.exUV (m + 1) (D.obj k2) _ _ h2
    obtain ⟨xi, hxi⟩ : ∃ xi : (X (m + 1)).obj c.pt, xi = ((X (m + 1)).map (c.ι.app k2)).hom x' := ⟨_, rfl⟩
    have hfd : ((S.f (m + 1)).app c.pt).hom (x - xi) = 0 := by
      rw [map_sub, hxi, natι (S.f (m + 1)), hx1, push, push, hu, sub_self]
    have hgd : ((S.g (m + 1)).app c.pt).hom (x - xi) = 0 := by
      rw [map_sub, hxi, natι (S.g (m + 1)), hx2, push, push, hv, sub_self]
    obtain ⟨w, hw⟩ := S.exX m c.pt _ hfd hgd
    obtain ⟨j3, w0, hw0⟩ := (hW m).1 w
    obtain ⟨k4, g3, g4, -⟩ := IsFilteredOrEmpty.cocone_objs k2 j3
    refine ⟨k4, ((X (m + 1)).map (D.map g3)).hom x' + ((X (m + 1)).map (D.map g4)).hom (((S.δ m).app (D.obj j3)).hom w0), ?_⟩
    rw [map_add, push, push, ← natι (S.δ m), hw0, hw, ← hxi]
    exact add_sub_cancel _ _
  · intro j y hy
    have hfy : ((U (m + 1)).map (c.ι.app j)).hom (((S.f (m + 1)).app (D.obj j)).hom y) = 0 := by
      rw [← natι (S.f (m + 1)), hy, map_zero]
    obtain ⟨k1, f1, h1⟩ := (hU (m + 1)).2 j _ hfy
    have hgy : ((V (m + 1)).map (c.ι.app k1)).hom
        (((V (m + 1)).map (D.map f1)).hom (((S.g (m + 1)).app (D.obj j)).hom y)) = 0 := by
      rw [push, ← natι (S.g (m + 1)), hy, map_zero]
    obtain ⟨k2, f2, h2⟩ := (hV (m + 1)).2 k1 _ hgy
    have hf1 : ((S.f (m + 1)).app (D.obj k2)).hom (((X (m + 1)).map (D.map (f1 ≫ f2))).hom y) = 0 := by
      rw [natap, D.map_comp, ← mapc, h1, map_zero]
    have hg1 : ((S.g (m + 1)).app (D.obj k2)).hom (((X (m + 1)).map (D.map (f1 ≫ f2))).hom y) = 0 := by
      rw [natap, D.map_comp, ← mapc, h2]
    obtain ⟨w, hw⟩ := S.exX m (D.obj k2) _ hf1 hg1
    have hdw : ((S.δ m).app c.pt).hom (((W m).map (c.ι.app k2)).hom w) = 0 := by
      rw [natι (S.δ m), hw, push, hy]
    obtain ⟨u, v, huv⟩ := (S.exW m c.pt _).1 hdw
    obtain ⟨j1, u0, hu0⟩ := (hU m).1 u
    obtain ⟨j2, v0, hv0⟩ := (hV m).1 v
    obtain ⟨k3, g1, g2, -⟩ := IsFilteredOrEmpty.cocone_objs j1 j2
    obtain ⟨k4, g3, g4, -⟩ := IsFilteredOrEmpty.cocone_objs k2 k3
    have he : ((W m).map (c.ι.app k4)).hom (((W m).map (D.map g3)).hom w -
        (((S.a m).app (D.obj k4)).hom (((U m).map (D.map (g1 ≫ g4))).hom u0) -
          ((S.b m).app (D.obj k4)).hom (((V m).map (D.map (g2 ≫ g4))).hom v0))) = 0 := by
      rw [map_sub, map_sub, push, ← natι (S.a m), ← natι (S.b m), push, push, hu0, hv0, huv, sub_self]
    obtain ⟨k5, g5, h5⟩ := (hW m).2 k4 _ he
    rw [map_sub, sub_eq_zero, mapc, map_sub, ← natap (S.a m), ← natap (S.b m)] at h5
    refine ⟨k5, (f1 ≫ f2) ≫ g3 ≫ g5, ?_⟩
    rw [D.map_comp, ← mapc, ← hw, ← natap (S.δ m), D.map_comp, h5]
    exact (S.exW m _ _).2 ⟨_, _, rfl⟩

theorem Five_of : LateralTheory.KummerTheory.ContCut.Five := by
  intro J _ _ K _ X U V W ⟨S⟩ D c hU hV hW n
  have := five_succ X U V W S c hU hV hW (n - 1)
  rwa [sub_add_cancel] at this

end LateralTheory.KummerTheory.FivePf
