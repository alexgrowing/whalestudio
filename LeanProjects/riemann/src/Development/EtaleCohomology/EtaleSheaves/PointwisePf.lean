import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.KillCokOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.PointwisePf

def PushColim : Prop := ∀ {D Y' O : CommRingCat.{0}} (φ' : D ⟶ Y') (o : D ⟶ O) {J : Type} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{0}) (t : (Functor.const J).obj D ⟶ F) (s : F ⟶ (Functor.const J).obj O),
  IsColimit (Cocone.mk O s) → (∀ j, t.app j ≫ s.app j = o) →
  ∃ (G : J ⥤ CommRingCat.{0}) (c : Cocone G) (_ : IsColimit c) (u : ∀ j, Y' ⟶ G.obj j) (ψ : ∀ j, F.obj j ⟶ G.obj j)
    (u'' : Y' ⟶ c.pt) (φ'' : O ⟶ c.pt),
    (∀ j, IsPushout φ' (t.app j) (u j) (ψ j)) ∧ (∀ {j k : J} (f : j ⟶ k), u j ≫ G.map f = u k) ∧
    (∀ {j k : J} (f : j ⟶ k), ψ j ≫ G.map f = F.map f ≫ ψ k) ∧ (∀ j, u j ≫ c.ι.app j = u'') ∧
    (∀ j, ψ j ≫ c.ι.app j = s.app j ≫ φ'') ∧ IsPushout φ' o u'' φ''

theorem pc (q : ℕ) (i m : ℤ) {X Y Z : CommRingCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (v : H (ZMod q) (sch.obj (Spec X)) (tw q i) m) :
    pull _ (sch.map (Spec.map g)) (tw q i) m (pull _ (sch.map (Spec.map f)) (tw q i) m v) =
      pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) m v := by
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

theorem unit_of {A B : CommRingCat.{0}} (h : A ⟶ B) (q : ℕ) (hq : IsUnit (q : A)) : IsUnit (q : B) := by
  have := hq.map h.hom; simpa using this

theorem Pointwise_of_pushColim (hPC : PushColim) : LateralTheory.E.KillCokPf.Pointwise := by
  intro hB1 q _ i A Y φ hq D d O o hIE hBC Y' w φ' hpo m y Q hQ
  obtain ⟨J, _, _, F, t, s, hs, ht⟩ := hIE
  have ho : ∀ j, t.app j ≫ s.app j = o := fun j => (ht j).2
  obtain ⟨G, c, hc, u, ψ, u'', φ'', hpj, hu, hψ, hcu, hcψ, hpo''⟩ := hPC φ' o F t s hs ho
  have hRE : RE q i φ'' := hBC _ (w ≫ u'') φ'' (hpo.paste_vert hpo'')
  obtain ⟨z, hz⟩ := (hRE m).2 (pull _ (sch.map (Spec.map u'')) (tw q i) m y)
  obtain ⟨j, zj, hzj⟩ := (hB1 q F (Cocone.mk O s) hs m i).1 z (unit_of (d ≫ o) q hq)
  change pull _ (sch.map (Spec.map (s.app j))) (tw q i) m zj = z at hzj
  let x : H (ZMod q) (sch.obj (Spec (G.obj j))) (tw q i) m :=
    pull _ (sch.map (Spec.map (u j))) (tw q i) m y - pull _ (sch.map (Spec.map (ψ j))) (tw q i) m zj
  have hx0 : pull _ (sch.map (Spec.map (c.ι.app j))) (tw q i) m x = 0 := by
    simp only [x, map_sub, pc, hcu, hcψ, ← hz, ← hzj]
    exact sub_self _
  obtain ⟨k, f, hk⟩ := (hB1 q G c hc m i).2 j x (unit_of (d ≫ t.app j ≫ ψ j) q hq) hx0
  change pull _ (sch.map (Spec.map (G.map f))) (tw q i) m x = 0 at hk
  refine ⟨F.obj k, t.app k, Q.comap (s.app k).hom, (ht k).1, Ideal.comap_isPrime _ _, ?_, G.obj k, u k, ψ k, hpj k,
    pull _ (sch.map (Spec.map (F.map f))) (tw q i) m zj, ?_⟩
  · rw [Ideal.comap_comap, ← ho k]; rfl
  · simp only [x, map_sub, pc, hu, hψ, sub_eq_zero] at hk
    rw [pc, hk]

@[simps]
def dgm {D : CommRingCat.{0}} {J : Type} [SmallCategory J] (F : J ⥤ CommRingCat.{0}) (t : (Functor.const J).obj D ⟶ F) :
    J ⥤ Under D where
  obj j := Under.mk (t.app j)
  map {j k} f := Under.homMk (F.map f) (by simpa using (t.naturality f).symm)
  map_id j := by ext; simp
  map_comp f g := by ext; simp

@[simps]
def cone {D O : CommRingCat.{0}} (o : D ⟶ O) {J : Type} [SmallCategory J] (F : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj D ⟶ F) (s : F ⟶ (Functor.const J).obj O) (ho : ∀ j, t.app j ≫ s.app j = o) :
    Cocone (dgm F t) where
  pt := Under.mk o
  ι := { app j := Under.homMk (s.app j) (by exact ho j)
         naturality j k f := by ext1; exact (s.naturality f).trans (Category.comp_id _) }

theorem pushColim : PushColim := by
  intro D Y' O φ' o J _ _ F t s hs ho
  have : ReflectsColimitsOfShape J (Under.forget D) := reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : (Under.pushout φ').IsLeftAdjoint := ⟨_, ⟨Under.mapPushoutAdj φ'⟩⟩
  have h1 : IsColimit ((Under.forget D).mapCocone (cone o F t s ho)) :=
    IsColimit.ofIsoColimit hs (Cocone.ext (Iso.refl _) (by intro j; exact Category.comp_id _))
  have hK : IsColimit (cone o F t s ho) := isColimitOfReflects (Under.forget D) h1
  have hP := isColimitOfPreserves (Under.pushout φ') hK
  have hc := isColimitOfPreserves (Under.forget Y') hP
  refine ⟨_, _, hc, fun j => pushout.inr (t.app j) φ', fun j => pushout.inl (t.app j) φ', pushout.inr o φ', pushout.inl o φ',
    fun j => (IsPushout.of_hasPushout (t.app j) φ').flip, ?_, ?_, ?_, ?_, (IsPushout.of_hasPushout o φ').flip⟩
  · intro j k f; simp [Under.pushout]; exact pushout.inr_desc _ _ _
  · intro j k f; simp [Under.pushout]; exact pushout.inl_desc _ _ _
  · intro j; simp [Under.pushout]; exact pushout.inr_desc _ _ _
  · intro j; simp [Under.pushout]; exact pushout.inl_desc _ _ _

end LateralTheory.E.PointwisePf

namespace LateralTheory.E.PointwisePf

theorem Pointwise_of : LateralTheory.E.KillCokPf.Pointwise := Pointwise_of_pushColim pushColim
end LateralTheory.E.PointwisePf
