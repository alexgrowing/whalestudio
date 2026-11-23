import Development.EtaleCohomology.CohomologicalPurity.LeafPBPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

abbrev evNU (n : ℕ) (U : Scheme.{0}) : Spc ⥤ Type :=
  (evaluation _ _).obj (op (SimplexCategory.mk n)) ⋙ (evaluation _ _).obj (op U)

theorem pb_ext {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) {n : ℕ} {U : Scheme.{0}} (x y : Sx (pullback f g) n U)
    (h1 : ((pullback.fst f g).app _).app _ x = ((pullback.fst f g).app _).app _ y)
    (h2 : ((pullback.snd f g).app _).app _ x = ((pullback.snd f g).app _).app _ y) : x = y := by
  let G := evNU n U
  let I := PreservesPullback.iso G f g ≪≫ Types.pullbackIsoPullback (G.map f) (G.map g)
  have hi : Function.Injective I.hom := (isIso_iff_bijective I.hom).1 inferInstance |>.1
  apply hi
  apply Subtype.ext
  have a1 := (ConcreteCategory.congr_hom (PreservesPullback.iso_hom_fst G f g))
  have a2 := (ConcreteCategory.congr_hom (PreservesPullback.iso_hom_snd G f g))
  refine Prod.ext ?_ ?_
  · simp only [I, Iso.trans_hom]
    rw [types_comp_apply, types_comp_apply, Types.pullbackIsoPullback_hom_fst, Types.pullbackIsoPullback_hom_fst]
    exact (a1 x).trans (h1.trans (a1 y).symm)
  · simp only [I, Iso.trans_hom]
    rw [types_comp_apply, types_comp_apply, Types.pullbackIsoPullback_hom_snd, Types.pullbackIsoPullback_hom_snd]
    exact (a2 x).trans (h2.trans (a2 y).symm)

theorem pb_mk {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) {n : ℕ} {U : Scheme.{0}} (a : Sx X n U) (b : Sx Y n U)
    (h : (f.app _).app _ a = (g.app _).app _ b) : ∃ x : Sx (pullback f g) n U,
    ((pullback.fst f g).app _).app _ x = a ∧ ((pullback.snd f g).app _).app _ x = b := by
  let G := evNU n U
  let z : Types.PullbackObj (G.map f) (G.map g) := ⟨(a, b), h⟩
  refine ⟨(PreservesPullback.iso G f g).inv ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z), ?_, ?_⟩
  · have := (ConcreteCategory.congr_hom (PreservesPullback.iso_inv_fst G f g))
      ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z)
    refine this.trans ?_
    exact (ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_fst (G.map f) (G.map g))) z
  · have := (ConcreteCategory.congr_hom (PreservesPullback.iso_inv_snd G f g))
      ((Types.pullbackIsoPullback (G.map f) (G.map g)).inv z)
    refine this.trans ?_
    exact (ConcreteCategory.congr_hom (Types.pullbackIsoPullback_inv_snd (G.map f) (G.map g))) z

theorem pr_ext {X Y : Spc} {n : ℕ} {U : Scheme.{0}} (x y : Sx (X ⨯ Y) n U)
    (h1 : ((prod.fst : X ⨯ Y ⟶ X).app _).app _ x = ((prod.fst : X ⨯ Y ⟶ X).app _).app _ y)
    (h2 : ((prod.snd : X ⨯ Y ⟶ Y).app _).app _ x = ((prod.snd : X ⨯ Y ⟶ Y).app _).app _ y) : x = y := by
  let G := evNU n U
  let I := PreservesLimitPair.iso G X Y ≪≫ Types.binaryProductIso (G.obj X) (G.obj Y)
  have hi : Function.Injective I.hom := (isIso_iff_bijective I.hom).1 inferInstance |>.1
  apply hi
  have a1 := (ConcreteCategory.congr_hom (prodComparison_fst G X Y))
  have a2 := (ConcreteCategory.congr_hom (prodComparison_snd G X Y))
  have b1 := (ConcreteCategory.congr_hom (Types.binaryProductIso_hom_comp_fst (G.obj X) (G.obj Y)))
  have b2 := (ConcreteCategory.congr_hom (Types.binaryProductIso_hom_comp_snd (G.obj X) (G.obj Y)))
  refine Prod.ext ?_ ?_
  · simp only [I, Iso.trans_hom, types_comp_apply, PreservesLimitPair.iso_hom]
    exact (b1 _).trans ((a1 x).trans (h1.trans ((a1 y).symm.trans (b1 _).symm)))
  · simp only [I, Iso.trans_hom, types_comp_apply, PreservesLimitPair.iso_hom]
    exact (b2 _).trans ((a2 x).trans (h2.trans ((a2 y).symm.trans (b2 _).symm)))

theorem um_basic {U : Scheme.{0}} {N : ℕ} (v : Fin N → Γ(U, ⊤)) (hv : Ideal.span (Set.range v) = ⊤) (p : U) :
    ∃ i : Fin N, 0 ≤ i.val ∧ p ∈ U.basicOpen (v i) := by
  have h := iSup_basicOpen_of_span_eq_top (X := U) ⊤ (Set.range v) hv
  have hp : p ∈ (⊤ : U.Opens) := trivial
  rw [← h] at hp
  obtain ⟨_, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  obtain ⟨⟨i, rfl⟩, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  exact ⟨i, Nat.zero_le _, hi⟩

theorem basic_um {A : Type} [CommRing A] {N : ℕ} (v : Fin N → Γ(Spec (CommRingCat.of A), ⊤))
    (hv : ∀ p, ∃ i : Fin N, 0 ≤ i.val ∧ p ∈ (Spec (CommRingCat.of A)).basicOpen (v i)) :
    Ideal.span (Set.range v) = ⊤ := by
  rw [← (isAffineOpen_top (Spec (CommRingCat.of A))).iSup_basicOpen_eq_self_iff]
  apply le_antisymm le_top
  intro p _
  obtain ⟨i, -, hi⟩ := hv p
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨v i, i, rfl⟩, hi⟩

def cstV (N : ℕ) (E : Spc) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (Functor.const (Fin (n.unop.len + 1))).obj (SingleObj.star (GL (Fin N) Γ(U.unop, ⊤)))
      naturality := fun U U' g => by
        ext x
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq ?_)
        exact (map_one (Matrix.GeneralLinearGroup.map _)).symm }
  naturality n m f := rfl

def conv {N n : ℕ} {U : Scheme.{0}} (c : ComposableArrows (Um N Γ(U, ⊤)) n)
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1) : ComposableArrows (Vec N 0 U) n where
  obj i := ⟨(c.obj i).1, um_basic _ (c.obj i).2⟩
  map {i j} h := ⟨(c.map h).1.2, fun k => by
    have := congrFun (c.map h).2 k
    rw [hc h] at this
    simpa using this⟩
  map_id i := Subtype.ext (congrArg (fun p => (Subtype.val p).2) (c.map_id i))
  map_comp f g := Subtype.ext (congrArg (fun p => (Subtype.val p).2) (c.map_comp f g))

theorem conv_congr {N n : ℕ} {U : Scheme.{0}} {c c' : ComposableArrows (Um N Γ(U, ⊤)) n} (e : c = c')
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1)
    (hc' : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c'.map h).1.1 = 1) : conv c hc = conv c' hc' := by
  subst e; rfl

theorem pb_gl {N : ℕ} {E : Spc} {n : SimplexCategoryᵒᵖ} {U : Scheme.{0}ᵒᵖ}
    (x : ((pullback (cstV N E) (PGL.pr N)).obj n).obj U) {i j : Fin (n.unop.len + 1)} (h : i ⟶ j) :
    ((((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x : ComposableArrows (Um N Γ(U.unop, ⊤)) n.unop.len).map h).1.1
      = 1 := by
  have e0 := ConcreteCategory.congr_hom
    (congrArg (fun φ : pullback (cstV N E) (PGL.pr N) ⟶ ofCat (glCat N) => (φ.app n).app U) (pullback.condition (f := cstV N E) (g := PGL.pr N))) x
  have e : ((Functor.const (Fin (n.unop.len + 1))).obj (SingleObj.star (GL (Fin N) Γ(U.unop, ⊤))) :
      ComposableArrows (SingleObj (GL (Fin N) Γ(U.unop, ⊤))) n.unop.len) =
      (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x : ComposableArrows (Um N Γ(U.unop, ⊤)) n.unop.len) ⋙
        Um.toGL N Γ(U.unop, ⊤) := e0
  have := Functor.congr_hom e.symm h
  exact this.trans ((Category.id_comp _).trans (Category.comp_id _))

def fMap (N : ℕ) (E : Spc) : pullback (cstV N E) (PGL.pr N) ⟶ Pj N 0 where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        (conv (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) (pb_gl x) : ComposableArrows (Vec N 0 U.unop) n.unop.len)
      naturality := fun U U' g => by
        ext x
        have e1 : (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U' (((pullback (cstV N E) (PGL.pr N)).obj n).map g x) :
            ComposableArrows (Um N Γ(U'.unop, ⊤)) n.unop.len) =
            ((PGL N).obj n).map g (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) :=
          ConcreteCategory.congr_hom (((pullback.snd (cstV N E) (PGL.pr N)).app n).naturality g) x
        refine (conv_congr e1 (pb_gl _) (by intro i j h; rw [← e1]; exact pb_gl _ h)).trans ?_
        exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl)) }
  naturality n m f := by
    ext U x
    have e1 : (((pullback.snd (cstV N E) (PGL.pr N)).app m).app U (((pullback (cstV N E) (PGL.pr N)).map f).app U x) :
        ComposableArrows (Um N Γ(U.unop, ⊤)) m.unop.len) =
        ((PGL N).map f).app U (((pullback.snd (cstV N E) (PGL.pr N)).app n).app U x) :=
      ConcreteCategory.congr_hom (congrArg (fun φ : (pullback (cstV N E) (PGL.pr N)).obj n ⟶ (PGL N).obj m => φ.app U) ((pullback.snd (cstV N E) (PGL.pr N)).naturality f)) x
    refine (conv_congr e1 (pb_gl _) (by intro i j h; rw [← e1]; exact pb_gl _ h)).trans ?_
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl))

def back {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n where
  obj i := ⟨(w.obj i).1, basic_um _ (w.obj i).2⟩
  map h := ⟨(1, (w.map h).1), by funext k; simpa using (w.map h).2 k⟩
  map_id i := Subtype.ext (Prod.ext rfl (congrArg Subtype.val (w.map_id i)))
  map_comp f g := Subtype.ext (Prod.ext (one_mul 1).symm (congrArg Subtype.val (w.map_comp f g)))

theorem back_conv {A : Type} [CommRing A] {N n : ℕ} (c : ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n)
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1) : back (conv c hc) = c :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ h => heq_of_eq (Subtype.ext (Prod.ext (hc h).symm rfl)))

theorem conv_back {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    conv (back w) (fun _ => rfl) = w :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq (Subtype.ext rfl))

theorem back_gl {A : Type} [CommRing A] {N n : ℕ} (w : ComposableArrows (Vec N 0 (Spec (CommRingCat.of A))) n) :
    ((Functor.const (Fin (n + 1))).obj (SingleObj.star (GL (Fin N) Γ(Spec (CommRingCat.of A), ⊤))) :
      ComposableArrows (SingleObj (GL (Fin N) Γ(Spec (CommRingCat.of A), ⊤))) n) = back w ⋙ Um.toGL N _ :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

theorem conv_inj {A : Type} [CommRing A] {N n : ℕ} {c c' : ComposableArrows (Um N Γ(Spec (CommRingCat.of A), ⊤)) n}
    (hc : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c.map h).1.1 = 1)
    (hc' : ∀ {i j : Fin (n + 1)} (h : i ⟶ j), (c'.map h).1.1 = 1) (e : conv c hc = conv c' hc') : c = c' :=
  (back_conv c hc).symm.trans ((congrArg back e).trans (back_conv c' hc'))

theorem fMap_line (N : ℕ) (E : Spc) : fMap N E ≫ Pj.line N 0 = pullback.snd (cstV N E) (PGL.pr N) ≫ PGL.line N := by
  ext n U x
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

theorem eMap_bij (N : ℕ) (R : Type) [CommRing R] (n : ℕ) (A : Type) [CommRing A] : Function.Bijective
      (fun x : Sx (pullback (cstV N (sp R)) (PGL.pr N)) n (Spec (CommRingCat.of A)) =>
        ((prod.lift (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)) : _ ⟶ PR N 0 R).app
          (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x) := by
  have k1 := fun z => ConcreteCategory.congr_hom (congrArg (fun φ : pullback (cstV N (sp R)) (PGL.pr N) ⟶ Pj N 0 =>
        (φ.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A)))) (prod.lift_fst (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)))) z
  have k2 := fun z => ConcreteCategory.congr_hom (congrArg (fun φ : pullback (cstV N (sp R)) (PGL.pr N) ⟶ sp R =>
        (φ.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A)))) (prod.lift_snd (fMap N (sp R)) (pullback.fst (cstV N (sp R)) (PGL.pr N)))) z
  constructor
  · intro x y hxy
    apply pb_ext
    · exact (k2 x).symm.trans ((congrArg _ hxy).trans (k2 y))
    · exact conv_inj (pb_gl x) (pb_gl y) ((k1 x).symm.trans ((congrArg _ hxy).trans (k1 y)))
  · intro z
    obtain ⟨x, hx1, hx2⟩ := pb_mk (cstV N (sp R)) (PGL.pr N) (n := n) (U := Spec (CommRingCat.of A))
      (((prod.snd : PR N 0 R ⟶ _).app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) z)
      (back (((prod.fst : PR N 0 R ⟶ _).app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) z))
      (back_gl _)
    refine ⟨x, pr_ext _ _ ?_ ?_⟩
    · exact (k1 x).trans ((conv_congr hx2 (pb_gl x) (fun _ => rfl)).trans (conv_back _))
    · exact (k2 x).trans hx1

theorem LeafPBMap_of : LeafPBMap := fun N R _ =>
  ⟨cstV N (sp R), prod.lift (fMap N (sp R)) (pullback.fst _ _), prod.lift_snd _ _,
    by rw [prod.lift_fst_assoc]; exact fMap_line N (sp R), fun n A _ => eMap_bij N R n A⟩

end LateralTheory.CohomologicalPurity.Thom
