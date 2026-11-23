import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.PbSp

private theorem hom_val {c : Act} {A : CommRingCat.{0}} {J : Type} [SmallCategory J] {F G : J ⥤ Ob c A} (h : F = G)
    {i j : J} (f : i ⟶ j) : (F.map f).1 = (G.map f).1 := by
  subst h
  rfl

private theorem law_id {P a : Act} (φ : Act.Hom P a) {A : CommRingCat.{0}} {J : Type} [SmallCategory J] (x : J ⥤ Ob a A)
    (j : J) : φ.g.app A 1 = (x.map (𝟙 j)).1 := by
  rw [x.map_id]
  exact map_one _

private theorem law_comp {P a : Act} (φ : Act.Hom P a) {A : CommRingCat.{0}} {J : Type} [SmallCategory J] (x : J ⥤ Ob a A)
    {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (p q : P.G.obj A) (hp : φ.g.app A p = (x.map f).1)
    (hq : φ.g.app A q = (x.map g).1) : φ.g.app A (p * q) = (x.map (f ≫ g)).1 := by
  rw [x.map_comp]
  change _ = (x.map f).1 * (x.map g).1
  rw [map_mul, hp, hq]

private theorem fn_square {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c)
    (A : CommRingCat.{0})
    (h1 : ∀ z : P.D.obj A, r.d.app A (t.d.app A z) = u.d.app A (l.d.app A z))
    (h2 : ∀ z : P.G.obj A, r.g.app A (t.g.app A z) = u.g.app A (l.g.app A z)) :
    t.fn A ⋙ r.fn A = l.fn A ⋙ u.fn A := by
  have ho : ∀ z : Ob P A, (t.fn A ⋙ r.fn A).obj z = (l.fn A ⋙ u.fn A).obj z :=
    fun z => congrArg Ob.mk (h1 z.pt)
  refine Functor.hext ho (fun z w f => ?_)
  exact Ob.hom_heq (ho z) (ho w) _ _ (h2 f.1)

private theorem lift_chain {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c)
    (A : CommRingCat.{0})
    (h3 : ∀ (x : a.D.obj A) (y : b.D.obj A), r.d.app A x = u.d.app A y → ∃! z : P.D.obj A, t.d.app A z = x ∧ l.d.app A z = y)
    (h4 : ∀ (g : a.G.obj A) (h : b.G.obj A), r.g.app A g = u.g.app A h → ∃! z : P.G.obj A, t.g.app A z = g ∧ l.g.app A z = h)
    {J : Type} [SmallCategory J] (x : J ⥤ Ob a A) (y : J ⥤ Ob b A) (h : x ⋙ r.fn A = y ⋙ u.fn A) :
    ∃! z : J ⥤ Ob P A, z ⋙ t.fn A = x ∧ z ⋙ l.fn A = y := by
  have hobj : ∀ j, r.d.app A (x.obj j).pt = u.d.app A (y.obj j).pt :=
    fun j => congrArg (fun F : J ⥤ Ob c A => (F.obj j).pt) h
  have hmap : ∀ (i j : J) (f : i ⟶ j), r.g.app A (x.map f).1 = u.g.app A (y.map f).1 :=
    fun i j f => hom_val h f
  choose zo hzo hzu using fun j => h3 (x.obj j).pt (y.obj j).pt (hobj j)
  choose zg hzg hzgu using fun (i j : J) (f : i ⟶ j) => h4 (x.map f).1 (y.map f).1 (hmap i j f)
  let F : J ⥤ Ob P A :=
    { obj := fun j => Ob.mk (zo j)
      map := fun {i j} f => ⟨zg i j f, by
        refine (hzu i _ ⟨?_, ?_⟩).symm
        · change t.d.app A (P.smul A (zg i j f) (zo j)) = _
          rw [t.eq, (hzg i j f).1, (hzo j).1]
          exact (x.map f).2.symm
        · change l.d.app A (P.smul A (zg i j f) (zo j)) = _
          rw [l.eq, (hzg i j f).2, (hzo j).2]
          exact (y.map f).2.symm⟩
      map_id := fun j => by
        apply Subtype.ext
        exact (hzgu j j (𝟙 j) 1 ⟨law_id t x j, law_id l y j⟩).symm
      map_comp := fun {i j k} f g => by
        apply Subtype.ext
        exact (hzgu i k (f ≫ g) (zg i j f * zg j k g)
          ⟨law_comp t x f g _ _ (hzg i j f).1 (hzg j k g).1,
            law_comp l y f g _ _ (hzg i j f).2 (hzg j k g).2⟩).symm }
  refine ⟨F, ⟨?_, ?_⟩, ?_⟩
  · have ho : ∀ j, (F ⋙ t.fn A).obj j = x.obj j := fun j => congrArg Ob.mk (hzo j).1
    exact Functor.hext ho (fun i j f => Ob.hom_heq (ho i) (ho j) _ _ (hzg i j f).1)
  · have ho : ∀ j, (F ⋙ l.fn A).obj j = y.obj j := fun j => congrArg Ob.mk (hzo j).2
    exact Functor.hext ho (fun i j f => Ob.hom_heq (ho i) (ho j) _ _ (hzg i j f).2)
  · rintro w ⟨hw1, hw2⟩
    have ho : ∀ j, w.obj j = F.obj j := fun j =>
      congrArg Ob.mk (hzu j (w.obj j).pt
        ⟨congrArg (fun G : J ⥤ Ob a A => (G.obj j).pt) hw1,
          congrArg (fun G : J ⥤ Ob b A => (G.obj j).pt) hw2⟩)
    exact Functor.hext ho (fun i j f =>
      Ob.hom_heq (ho i) (ho j) _ _ (hzgu i j f (w.map f).1 ⟨hom_val hw1 f, hom_val hw2 f⟩))

private abbrev Ch (a : Act) (k : ℕ) (T : Scheme.{0}) : Type := Fin (k + 1) ⥤ Ob a (Scheme.Γ.obj (op T))

private def pr1 {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (s : Sx (Sp E a) k T) : Sx E k T :=
  Prod.fst (α := Sx E k T) (β := Ch a k T) s

private def pr2 {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (s : Sx (Sp E a) k T) : Ch a k T :=
  Prod.snd (α := Sx E k T) (β := Ch a k T) s

private def mkS {E : Spc} {a : Act} {k : ℕ} {T : Scheme.{0}} (e : Sx E k T) (x : Ch a k T) : Sx (Sp E a) k T :=
  Prod.mk (α := Sx E k T) (β := Ch a k T) e x

end UpperTheory.PbSp

open UpperTheory.PbSp in
theorem UpperTheory.stackProduct_isPullback_of_actionPullback :
    ∀ (E : Spc) {P a b c : Act} (t : Act.Hom P a) (l : Act.Hom P b) (r : Act.Hom a c) (u : Act.Hom b c),
        (∀ A (z : P.D.obj A), r.d.app A (t.d.app A z) = u.d.app A (l.d.app A z)) →
        (∀ A (z : P.G.obj A), r.g.app A (t.g.app A z) = u.g.app A (l.g.app A z)) →
        (∀ A (x : a.D.obj A) (y : b.D.obj A), r.d.app A x = u.d.app A y → ∃! z : P.D.obj A, t.d.app A z = x ∧ l.d.app A z = y) →
        (∀ A (g : a.G.obj A) (h : b.G.obj A), r.g.app A g = u.g.app A h → ∃! z : P.G.obj A, t.g.app A z = g ∧ l.g.app A z = h) →
        IsPullback (Sp.map E t) (Sp.map E l) (Sp.map E r) (Sp.map E u) := by
  intro E P a b c t l r u h1 h2 h3 h4
  have hsq : ∀ A, t.fn A ⋙ r.fn A = l.fn A ⋙ u.fn A := fun A => fn_square t l r u A (h1 A) (h2 A)
  apply isPullback_of_unique_simplices_pullback
  · ext k T s
    refine Prod.ext rfl ?_
    exact congrArg (fun F => s.2 ⋙ F) (hsq _)
  · intro k T x y hxy
    have e1 : pr1 x = pr1 y := congrArg pr1 hxy
    have e2 : pr2 x ⋙ r.fn _ = pr2 y ⋙ u.fn _ := congrArg pr2 hxy
    obtain ⟨z, ⟨hz1, hz2⟩, hzu⟩ := lift_chain t l r u _ (h3 _) (h4 _) (pr2 x) (pr2 y) e2
    refine ⟨mkS (pr1 x) z, ⟨?_, ?_⟩, ?_⟩
    · change mkS (pr1 x) (z ⋙ t.fn _) = x
      rw [hz1]
      rfl
    · change mkS (pr1 x) (z ⋙ l.fn _) = y
      rw [hz2, e1]
      rfl
    · rintro w ⟨hw1, hw2⟩
      have f1 : pr1 w = pr1 x := congrArg pr1 hw1
      have f2 : pr2 w = z := hzu _ ⟨congrArg pr2 hw1, congrArg pr2 hw2⟩
      change mkS (pr1 w) (pr2 w) = mkS (pr1 x) z
      rw [f1, f2]
