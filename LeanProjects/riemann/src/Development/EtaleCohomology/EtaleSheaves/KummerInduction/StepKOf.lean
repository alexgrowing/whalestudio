import Development.EtaleCohomology.EtaleSheaves.KummerInduction

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.ContStepPf LateralTheory.E.StepKPf

namespace LateralTheory.E.StepKPf.ChasePf

variable {J : Type} [SmallCategory J]

def ChaseB : Prop := Hyp → MV → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0})
  (c : Cone D), IsLimit c → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X) (U V : X.Opens), U ⊔ V = ⊤ →
  RC q c e U → RC q c e V → RC q c e (U ⊓ V) →
  ∀ (n i : ℤ) (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (D.obj k)) n i), pull _ (sch.map (c.π.app k)) _ _ y = 0 →
    pull _ (sch.map (lv D e U f).ι) _ _ y = 0 → pull _ (sch.map (lv D e V f).ι) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map (D.map g)) _ _ y = 0

theorem rL_ι {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J}
    (f : k ⟶ j0) : rL c e U f ≫ (lv D e U f).ι = (lm c e U).ι ≫ c.π.app k :=
  Scheme.Hom.resLE_comp_ι _ _

theorem rD_ι (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : rD D e U f g ≫ (lv D e U f).ι = (lv D e U (g ≫ f)).ι ≫ D.map g :=
  Scheme.Hom.resLE_comp_ι _ _

theorem kerU {q : ℕ} {D : J ⥤ Scheme.{0}} {c : Cone D} {j0 : J} {X : Scheme.{0}} {e : D.obj j0 ≅ X} {U : X.Opens}
    (hR : RC q c e U) {n i : ℤ} {k : J} (f : k ⟶ j0) (y : Ht q (sch.obj (D.obj k)) n i)
    (hy : pull _ (sch.map (c.π.app k)) _ _ y = 0) : ∃ (l : J) (a : l ⟶ k),
      pull _ (sch.map (lv D e U (a ≫ f)).ι) _ _ (pull _ (sch.map (D.map a)) _ _ y) = 0 := by
  have h0 : pull _ (sch.map (rL c e U f)) _ _ (pull _ (sch.map (lv D e U f).ι) _ _ y) = 0 := by
    rw [← pull_comp, ← Functor.map_comp, rL_ι, Functor.map_comp, pull_comp, hy, map_zero]
  obtain ⟨l, a, ha⟩ := (hR n i).2 k f _ h0
  refine ⟨l, a, ?_⟩
  rw [← pull_comp, ← Functor.map_comp, ← rD_ι, Functor.map_comp, pull_comp, ha]

theorem stab {q : ℕ} (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {n i : ℤ}
    {k l l' : J} (f : k ⟶ j0) (y : Ht q (sch.obj (D.obj k)) n i) (a : l ⟶ k) (m : l' ⟶ l) (g : l' ⟶ k) (hg : g = m ≫ a)
    (h : pull _ (sch.map (lv D e U (a ≫ f)).ι) _ _ (pull _ (sch.map (D.map a)) _ _ y) = 0) :
    pull _ (sch.map (lv D e U (g ≫ f)).ι) _ _ (pull _ (sch.map (D.map g)) _ _ y) = 0 := by
  subst hg
  have e1 : (m ≫ a) ≫ f = m ≫ (a ≫ f) := Category.assoc _ _ _
  rw [e1, D.map_comp, Functor.map_comp, pull_comp, ← pull_comp, ← Functor.map_comp, ← rD_ι, Functor.map_comp,
    pull_comp, h, map_zero]

theorem Chase_of (hB : ChaseB) : DiagramChase₂ := by
  intro h hmv q J _ _ D c hc j0 X e U V hUV rU rV rW n i k f y hy
  obtain ⟨l1, a, ha⟩ := kerU rU f y hy
  obtain ⟨l2, b, hb⟩ := kerU rV f y hy
  let p := IsCofiltered.minToLeft l1 l2
  let r := IsCofiltered.minToRight l1 l2
  let m := IsCofiltered.eqHom (p ≫ a) (r ≫ b)
  have hm : m ≫ p ≫ a = m ≫ r ≫ b := IsCofiltered.eq_condition _ _
  let g := m ≫ p ≫ a
  have hU := stab D e U f y a (m ≫ p) g (by simp only [g, Category.assoc]) ha
  have hV := stab D e V f y b (m ≫ r) g (by simp only [g, Category.assoc]; exact hm) hb
  have hy' : pull _ (sch.map (c.π.app _)) _ _ (pull _ (sch.map (D.map g)) _ _ y) = 0 := by
    rw [← pull_comp, ← Functor.map_comp, c.w]; exact hy
  obtain ⟨l, g', hg'⟩ := hB h hmv q D c hc j0 X e U V hUV rU rV rW n i _ (g ≫ f) _ hy' hU hV
  exact ⟨l, g' ≫ g, by rw [D.map_comp, Functor.map_comp, pull_comp]; exact hg'⟩

theorem StepK_of' (hR : Restr) (hB : ChaseB) : StepK := StepK_of hR (Chase_of hB)

end LateralTheory.E.StepKPf.ChasePf
