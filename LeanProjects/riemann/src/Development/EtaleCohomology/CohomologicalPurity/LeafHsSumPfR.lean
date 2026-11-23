import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafDblSum : Prop := ∀ (X : Scheme.{0}) (U : X.Opens) (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ (π : c.pt ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X)
  (h : ∀ a, disc.map (c.inj a) ≫ disc.map π = disc.map (π' a)),
  Nonempty (IsColimit (Cofan.mk (dbl (abv U (E := disc.obj c.pt) (disc.map π)))
    fun a => dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))))

def LeafDiscSumH : Prop := ∀ (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  Nonempty (IsColimit (Cofan.mk (disc.obj c.pt) fun a => disc.map (c.inj a)))

theorem leafDiscSumH : LeafDiscSumH := fun A E c hc =>
  ⟨isColimitCofanMkObjOfIsColimit disc E (fun a => c.inj a)
    (hc.some.ofIsoColimit (Cofan.ext (Iso.refl _) (fun _ => by simp)))⟩

def LeafPbSum : Prop := ∀ (X : Scheme.{0}) (U : X.Opens) (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ (π : c.pt ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X)
  (h : ∀ a, disc.map (c.inj a) ≫ disc.map π = disc.map (π' a)),
  Nonempty (IsColimit (Cofan.mk (abv U (E := disc.obj c.pt) (disc.map π)).left
    fun a => (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left))

theorem dbl_inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc _ _ _

theorem dbl_inl_map_assoc {P' P : Arrow Spc} (φ : P' ⟶ P) {Z : Spc} (h : dbl P ⟶ Z) :
    dbl.inl P' ≫ dbl.map φ ≫ h = φ.right ≫ dbl.inl P ≫ h := by
  rw [← Category.assoc, dbl_inl_map, Category.assoc]

theorem dbl_inr_map_assoc {P' P : Arrow Spc} (φ : P' ⟶ P) {Z : Spc} (h : dbl P ⟶ Z) :
    dbl.inr P' ≫ dbl.map φ ≫ h = φ.right ≫ dbl.inr P ≫ h := by
  rw [← Category.assoc, dbl.inr_map, Category.assoc]

def dbl_cofan {A : Type} {P : Arrow Spc} (Q : A → Arrow Spc) (φ : ∀ a, Q a ⟶ P)
    (hl : IsColimit (Cofan.mk P.left fun a => (φ a).left)) (hr : IsColimit (Cofan.mk P.right fun a => (φ a).right)) :
    IsColimit (Cofan.mk (dbl P) fun a => dbl.map (φ a)) := by
  refine mkCofanColimit _ (fun s => pushout.desc (Cofan.IsColimit.desc hr fun a => dbl.inl (Q a) ≫ s.inj a)
      (Cofan.IsColimit.desc hr fun a => dbl.inr (Q a) ≫ s.inj a) ?_) ?_ ?_
  · refine Cofan.IsColimit.hom_ext hl _ _ fun a => ?_
    have w := Arrow.w (φ a)
    have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a :=
      Cofan.IsColimit.fac hr _ a
    have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a :=
      Cofan.IsColimit.fac hr _ a
    change ((φ a).left ≫ P.hom) ≫ _ = ((φ a).left ≫ P.hom) ≫ _
    rw [w, Category.assoc, Category.assoc, f1, f2, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ s.inj a) (pushout.condition)
  · intro s a
    have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a := by
      simpa using Cofan.IsColimit.fac hr (fun a => dbl.inl (Q a) ≫ s.inj a) a
    have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a := by
      simpa using Cofan.IsColimit.fac hr (fun a => dbl.inr (Q a) ≫ s.inj a) a
    apply pushout.hom_ext
    · exact (dbl_inl_map_assoc (φ a) _).trans ((congrArg _ (pushout.inl_desc _ _ _)).trans f1)
    · exact (dbl_inr_map_assoc (φ a) _).trans ((congrArg _ (pushout.inr_desc _ _ _)).trans f2)
  · intro s m hm
    apply pushout.hom_ext
    · refine Eq.trans ?_ (pushout.inl_desc _ _ _).symm
      refine Cofan.IsColimit.hom_ext hr _ _ fun a => ?_
      have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a := by
        simpa using Cofan.IsColimit.fac hr (fun a => dbl.inl (Q a) ≫ s.inj a) a
      refine Eq.trans ?_ f1.symm
      exact (dbl_inl_map_assoc (φ a) m).symm.trans (congrArg _ (hm a))
    · refine Eq.trans ?_ (pushout.inr_desc _ _ _).symm
      refine Cofan.IsColimit.hom_ext hr _ _ fun a => ?_
      have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a := by
        simpa using Cofan.IsColimit.fac hr (fun a => dbl.inr (Q a) ≫ s.inj a) a
      refine Eq.trans ?_ f2.symm
      exact (dbl_inr_map_assoc (φ a) m).symm.trans (congrArg _ (hm a))

theorem leafDblSum_of (hP : LeafPbSum) : LeafDblSum := fun X U A E c hc π π' h =>
  ⟨dbl_cofan _ _ (hP X U A E c hc π π' h).some (leafDiscSumH A E c hc).some⟩

theorem LeafHsSum_of_dbl (hS : LeafSum) (hD : LeafDblSum) (hd : LeafDiscSumH) : LeafHsSum := by
  intro q X U A E c hc π π' h n i
  have S1 := hS (ZMod q) (tw q i) A _ _ (hD X U A E c hc π π' h) n
  have S2 := hS (ZMod q) (tw q i) A _ _ (hd A E c hc) n
  constructor
  · intro x y e
    apply Subtype.ext
    apply S1.1
    funext a
    exact congrArg Subtype.val (congrFun e a)
  · intro y
    obtain ⟨x, hx⟩ := S1.2 (fun a => (y a).1)
    have hx' : ∀ a, pull _ (dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))) (tw q i) n x
        = (y a).1 := fun a => congrFun hx a
    have m : x ∈ Hs q (abv U (E := disc.obj c.pt) (disc.map π)) n i := by
      refine AddMonoidHom.mem_ker.mpr ?_
      apply S2.1
      funext a
      have e := dbl.inr_map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))
      have y0 : pull _ (dbl.inr _) (tw q i) n (y a).1 = 0 := (y a).2
      have e2 : disc.map (c.inj a) ≫ dbl.inr (abv U (E := disc.obj c.pt) (disc.map π)) =
          dbl.inr _ ≫ dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)) := e.symm
      have key : pull _ (disc.map (c.inj a) ≫ dbl.inr (abv U (E := disc.obj c.pt) (disc.map π))) (tw q i) n x = 0 := by
        exact (congrArg (fun f => pull (ZMod q) f (tw q i) n x) e2).trans ((pull_comp _ _ _ _ _ _).trans
          ((congrArg (pull (ZMod q) (dbl.inr _) (tw q i) n) (hx' a)).trans y0))
      exact ((pull_comp _ _ _ _ _ _).symm.trans key).trans (map_zero _).symm
    exact ⟨⟨x, m⟩, funext fun a => Subtype.ext (hx' a)⟩

end LateralTheory.CohomologicalPurity.TubeCut

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem LeafHsSum_of (hS : LeafSum) (hP : LeafPbSum) : LeafHsSum := LeafHsSum_of_dbl hS (leafDblSum_of hP) leafDiscSumH
end LateralTheory.CohomologicalPurity.TubeCut
