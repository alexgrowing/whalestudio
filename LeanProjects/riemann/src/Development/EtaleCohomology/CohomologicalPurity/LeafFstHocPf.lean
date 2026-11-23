import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafDiscPb : Prop := ∀ {A Y G : PSh} (f : A ⟶ Y) (g : G ⟶ Y),
  ∃ e : disc.obj (pullback f g) ≅ pullback (disc.map f) (disc.map g), e.hom ≫ pullback.fst _ _ = disc.map (pullback.fst f g)

def DiscreteSimplicialPresheafPreservesCoproducts : Prop := ∀ (A : Type) (X : A → PSh) (c : Cofan X), Nonempty (IsColimit c) →
  Nonempty (IsColimit (Cofan.mk (disc.obj c.pt) fun a => disc.map (c.inj a)))

def LeafUnivSum : Prop := ∀ (A : Type) (X : A → PSh) (c : Cofan X), Nonempty (IsColimit c) → ∀ {Y G : PSh} (f : c.pt ⟶ Y)
  (g : G ⟶ Y), Nonempty (IsColimit (Cofan.mk (pullback f g)
    fun a => pullback.map (c.inj a ≫ f) g f g (c.inj a) (𝟙 G) (𝟙 Y) (by simp) (by simp)))

instance discPres (n : SimplexCategoryᵒᵖ) {K : Type} [SmallCategory K] (G : K ⥤ PSh) :
    PreservesLimit G (disc ⋙ (evaluation _ _).obj n) :=
  preservesLimit_of_natIso G (NatIso.ofComponents (fun X => Iso.refl X) (fun _ => rfl) : 𝟭 PSh ≅ disc ⋙ (evaluation _ _).obj n)

instance discPresC (n : SimplexCategoryᵒᵖ) {K : Type} [SmallCategory K] (G : K ⥤ PSh) :
    PreservesColimit G (disc ⋙ (evaluation _ _).obj n) :=
  preservesColimit_of_natIso G (NatIso.ofComponents (fun X => Iso.refl X) (fun _ => rfl) : 𝟭 PSh ≅ disc ⋙ (evaluation _ _).obj n)

instance {K : Type} [SmallCategory K] (G : K ⥤ PSh) : PreservesLimit G disc := preservesLimit_of_evaluation _ _ fun _ => inferInstance
instance {K : Type} [SmallCategory K] (G : K ⥤ PSh) : PreservesColimit G disc := preservesColimit_of_evaluation _ _ fun _ => inferInstance

theorem leafDiscPb : LeafDiscPb := fun f g => ⟨PreservesPullback.iso disc f g, PreservesPullback.iso_hom_fst _ _ _⟩

theorem leafDiscSum_ryrx : DiscreteSimplicialPresheafPreservesCoproducts := fun _ X c ⟨h⟩ =>
  ⟨(isColimitMapCoconeCofanMkEquiv disc X c.inj).1 (isColimitOfPreserves disc h)⟩

theorem eqv_sum (hS : LeafSum) {R : Type} [CommRing R] (F : Shv R) {A : Type} {E' E : A → Spc} (c' : Cofan E')
    (c : Cofan E) (h' : Nonempty (IsColimit c')) (h : Nonempty (IsColimit c)) (f : c'.pt ⟶ c.pt)
    (fa : ∀ a, E' a ⟶ E a) (hf : ∀ a, c'.inj a ≫ f = fa a ≫ c.inj a) (he : ∀ a, Eqv R (fa a) F) : Eqv R f F := fun n => by
  have k : (fun x a => pull R (c'.inj a) F n x) ∘ pull R f F n =
      (fun (y : ∀ a, H R (E a) F n) a => pull R (fa a) F n (y a)) ∘ (fun x a => pull R (c.inj a) F n x) := by
    funext x a
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, hf]
  have bp : Function.Bijective (fun (y : ∀ a, H R (E a) F n) a => pull R (fa a) F n (y a)) :=
    ⟨fun y z e => funext fun a => (he a n).1 (congrFun e a),
     fun w => ⟨fun a => ((he a n).2 (w a)).choose, funext fun a => ((he a n).2 (w a)).choose_spec⟩⟩
  have b2 := bp.comp (hS R F A E c h n)
  rw [← k] at b2
  exact (Function.Bijective.of_comp_iff' (hS R F A E' c' h' n) _).1 b2

theorem inj_aug {J : Type} [SmallCategory J] (D : J ⥤ PSh) {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c)
    (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) : inj D n σ ≫ (aug c hc).app n = c (σ.obj 0) := by
  have e : σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _ := σ.map_id _
  ext U x
  change (c (σ.obj 0)).app U ((D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U x) = (c (σ.obj 0)).app U x
  rw [e, D.map_id]
  rfl

theorem etale_first_hocolim_descent_of_discrete_pullback_sum (hL : LeafLevel) (hS : LeafSum) (hP : LeafDiscPb) (hD : DiscreteSimplicialPresheafPreservesCoproducts) (hU : LeafUnivSum) :
    LeafFstHoc := by
  intro hA3 R _ F J _ D Y G g c hc hj
  apply hA3
  intro n
  have e1 : disc.map ((pullback.fst (aug c hc) (disc.map g)).app n) =
      disc.map (pullbackObjIso (aug c hc) (disc.map g) n).hom ≫
        disc.map (pullback.fst ((aug c hc).app n) ((disc.map g).app n)) := by
    rw [← disc.map_comp, pullbackObjIso_hom_comp_fst]
  rw [e1]
  refine eqv_comp (eqv_iso _ _) ?_
  obtain ⟨hLc⟩ := hL J D n
  have hU' := hU _ _ _ ⟨hLc⟩ ((aug c hc).app n) ((disc.map g).app n)
  refine eqv_sum hS F _ _ (hD _ _ _ hU') (hD _ _ _ ⟨hLc⟩) _
    (fun σ => disc.map (pullback.fst (inj D n σ ≫ (aug c hc).app n) ((disc.map g).app n))) ?_ ?_
  · intro σ
    show disc.map _ ≫ disc.map _ = disc.map _ ≫ disc.map _
    refine ((disc.map_comp _ _).symm.trans (congrArg disc.map ?_)).trans (disc.map_comp _ _)
    exact pullback.lift_fst _ _ _
  · intro σ
    have h0 := hj (σ.obj 0)
    obtain ⟨e, he⟩ := hP (c (σ.obj 0)) g
    have E := inj_aug D c hc n σ
    have key : ∀ f (_ : f = c (σ.obj 0)), Eqv R (disc.map (pullback.fst f g)) F := by
      rintro f rfl
      rw [← he]
      exact eqv_comp (eqv_iso _ _) h0
    exact key _ E

theorem LeafFstHoc_of (hL : LeafLevel) (hS : LeafSum) (hU : LeafUnivSum) : LeafFstHoc :=
  etale_first_hocolim_descent_of_discrete_pullback_sum hL hS leafDiscPb leafDiscSum_ryrx hU

end LateralTheory.CohomologicalPurity.TubeCut
