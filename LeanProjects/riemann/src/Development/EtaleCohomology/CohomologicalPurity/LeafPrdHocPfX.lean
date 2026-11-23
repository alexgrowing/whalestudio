import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem sq (AN : LeafActNat) (a6 : DivisorNaturality) (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (f : E' ⟶ E)
    (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X) (h : f ≫ π = π') {n m i k : ℤ} (x : Ht q E n i) (b : Hs q (opn U) m k) :
    Hs.pull q (abvRel U f π' π h) _ _ (Hs.act q (P := abv U π) x (Hs.pull q (abvMap U π) _ _ b)) =
      Hs.act q (P := abv U π') (pull _ f _ _ x) (Hs.pull q (abvMap U π') _ _ b) := by
  have e := AN a6 q _ _ (abvRel U f π' π h) n m i k x (Hs.pull q (abvMap U π) _ _ b)
  rw [← hs_pull_comp, abvRel_abvMap] at e
  exact e

theorem prd_sum (S : LeafSum) (HS : LeafHsSum) (AN : LeafActNat) (a6 : DivisorNaturality) (q : ℕ) [NeZero q] {X : Scheme.{0}}
    (U : X.Opens) {A : Type} (E : A → PSh) (P : PSh) (g : ∀ a, E a ⟶ P) (t : IsColimit (Cofan.mk P g))
    (π : P ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X) (h : ∀ a, g a ≫ π = π' a) {m k : ℤ} (b : Hs q (opn U) m k)
    (hb : ∀ a, Prd q U (E := disc.obj (E a)) (disc.map (π' a)) b) :
    Prd q U (E := disc.obj P) (disc.map π) b := by
  intro n i
  have h' : ∀ a, disc.map ((Cofan.mk P g).inj a) ≫ disc.map π = disc.map (π' a) := fun a => by
    rw [← disc.map_comp]; exact congrArg disc.map (h a)
  have tS : IsColimit (Cofan.mk (disc.obj P) fun a => disc.map (g a)) := isColimitCofanMkObjOfIsColimit disc E g t
  have hΦ := S (ZMod q) (tw q i) A (fun a => disc.obj (E a)) _ ⟨tS⟩ n
  have hΨ := HS q X U A E (Cofan.mk P g) ⟨t⟩ π π' h' (n + m) (i + k)
  have hP : Function.Bijective (Pi.map fun a (x : Ht q (disc.obj (E a)) n i) =>
      Hs.act q (P := abv U (disc.map (π' a))) x (Hs.pull q (abvMap U (disc.map (π' a))) _ _ b)) :=
    Function.Bijective.piMap fun a => hb a n i
  refine (Function.Bijective.of_comp_iff' hΨ _).1 ?_
  convert hP.comp hΦ using 1
  all_goals try rfl
  funext x
  funext a
  exact sq AN a6 q U _ _ _ (h' a) x b

theorem inj_aug_RPrdH {J : Type} [SmallCategory J] (D : J ⥤ PSh) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ yoneda.obj X)
    (hc : Coc D c) (N : SimplexCategoryᵒᵖ) (σ : Fin (N.unop.len + 1) ⥤ J) :
    inj D N σ ≫ ((aug c hc).app N : (hoc D).obj N ⟶ yoneda.obj X) = c (σ.obj 0) := by
  ext U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (hc _ _ (σ.map (homOfLE (Fin.zero_le 0)))) U) x

theorem LeafPrdHoc_of (lvl : LeafPrdLevel) (L : LeafLevel) (S : LeafSum) (HS : LeafHsSum) (AN : LeafActNat) :
    LeafPrdHoc := by
  intro hyp q _ J _ D X U c hc m k b hb
  refine lvl hyp q X U _ (aug c hc) m k b fun N => ?_
  exact prd_sum S HS AN hyp.2.2.2.2.1 q U (fun σ : Fin (N.unop.len + 1) ⥤ J => D.obj (σ.obj 0)) ((hoc D).obj N)
    (inj D N) (L J D N).some ((aug c hc).app N : (hoc D).obj N ⟶ yoneda.obj X)
    (fun σ : Fin (N.unop.len + 1) ⥤ J => c (σ.obj 0)) (inj_aug_RPrdH D c hc N) b
    (fun σ : Fin (N.unop.len + 1) ⥤ J => hb (σ.obj 0))

end LateralTheory.CohomologicalPurity.TubeCut
