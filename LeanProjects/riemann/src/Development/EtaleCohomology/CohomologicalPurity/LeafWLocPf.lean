import Development.EtaleCohomology.CohomologicalPurity.LeafWCovPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem prod_elt_bij (A B : Spc) (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ) :
    Function.Bijective (fun z : ((A ⨯ B).obj n).obj X =>
      (((prod.fst : A ⨯ B ⟶ A).app n).app X z, ((prod.snd : A ⨯ B ⟶ B).app n).app X z)) := by
  let G : Spc ⥤ Type := (evaluation _ _).obj n ⋙ (evaluation _ _).obj X
  let f := (PreservesLimitPair.iso G A B).hom ≫ (Types.binaryProductIso _ _).hom
  have hf : Function.Bijective f := (isIso_iff_bijective f).1 inferInstance
  have h1 : f ≫ TypeCat.ofHom (Prod.fst : G.obj A × G.obj B → G.obj A) = G.map prod.fst := by
    simp [f, PreservesLimitPair.iso_hom]
  have h2 : f ≫ TypeCat.ofHom (Prod.snd : G.obj A × G.obj B → G.obj B) = G.map prod.snd := by
    simp [f, PreservesLimitPair.iso_hom]
  have e : (fun z : ((A ⨯ B).obj n).obj X =>
      (((prod.fst : A ⨯ B ⟶ A).app n).app X z, ((prod.snd : A ⨯ B ⟶ B).app n).app X z)) = ⇑(ConcreteCategory.hom f) := by
    funext z
    refine Prod.ext ?_ ?_
    · exact (congrArg (fun φ => φ z) h1).symm
    · exact (congrArg (fun φ => φ z) h2).symm
  rw [e]; exact hf

def liftW {C : Type} [Category C] {d : ℕ} {U : Scheme.{0}} (F : C ⥤ Vec (d + 1) 0 U)
    (h : ∀ c, IsUnit ((F.obj c).1 0)) : C ⥤ WVec d U where
  obj c := ⟨F.obj c, h c⟩
  map f := F.map f
  map_id c := F.map_id c
  map_comp f g := F.map_comp f g

def lift1 {C : Type} [Category C] {N : ℕ} {U : Scheme.{0}} (F : C ⥤ Vec N 0 U)
    (h : ∀ c (p : U), ∃ i : Fin N, 1 ≤ i.val ∧ p ∈ U.basicOpen ((F.obj c).1 i)) : C ⥤ Vec N 1 U where
  obj c := ⟨(F.obj c).1, h c⟩
  map f := F.map f
  map_id c := F.map_id c
  map_comp f g := F.map_comp f g

theorem bo_hom {N k : ℕ} {U : Scheme.{0}} {v w : Vec N k U} (u : v ⟶ w) (i : Fin N) :
    U.basicOpen (v.1 i) = U.basicOpen (w.1 i) := by
  obtain ⟨u, hu⟩ := u
  rw [hu i, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ u.isUnit, top_inf_eq]

theorem bo_chain {N k m : ℕ} {U : Scheme.{0}} (c : ComposableArrows (Vec N k U) m) (a : Fin (m + 1)) (i : Fin N) :
    U.basicOpen ((c.obj a).1 i) = U.basicOpen ((c.obj 0).1 i) :=
  (bo_hom (c.map (homOfLE (Fin.zero_le a))) i).symm

theorem mem_bo_map {N k : ℕ} {X : Scheme.{0}} (O : X.Opens) (v : Vec N k X) (i : Fin N) (p : (O : Scheme.{0})) :
    p ∈ (O : Scheme.{0}).basicOpen (((Vec.map N k O.ι).obj v).1 i) ↔ p.val ∈ X.basicOpen (v.1 i) := by
  change p ∈ (O : Scheme.{0}).basicOpen (O.ι.appTop.hom (v.1 i)) ↔ _
  rw [← Scheme.preimage_basicOpen_top]
  rfl

theorem isUnit_of_bo {Y : Scheme.{0}} (f : Γ(Y, ⊤)) (h : ∀ p : Y, p ∈ Y.basicOpen f) : IsUnit f :=
  Y.toRingedSpace.isUnit_of_isUnit_germ ⊤ f fun x _ => (Y.mem_basicOpen_top f x).1 (h x)

theorem fst_map {A B : Spc} (n : SimplexCategoryᵒᵖ) {X Y : Scheme.{0}ᵒᵖ} (f : X ⟶ Y) (z : ((A ⨯ B).obj n).obj X) :
    ((prod.fst : A ⨯ B ⟶ A).app n).app Y (((A ⨯ B).obj n).map f z) =
      (A.obj n).map f (((prod.fst : A ⨯ B ⟶ A).app n).app X z) :=
  NatTrans.naturality_apply ((prod.fst : A ⨯ B ⟶ A).app n) f z

theorem snd_map {A B : Spc} (n : SimplexCategoryᵒᵖ) {X Y : Scheme.{0}ᵒᵖ} (f : X ⟶ Y) (z : ((A ⨯ B).obj n).obj X) :
    ((prod.snd : A ⨯ B ⟶ B).app n).app Y (((A ⨯ B).obj n).map f z) =
      (B.obj n).map f (((prod.snd : A ⨯ B ⟶ B).app n).app X z) :=
  NatTrans.naturality_apply ((prod.snd : A ⨯ B ⟶ B).app n) f z

theorem map_fst_app {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ)
    (z : ((A ⨯ B).obj n).obj X) :
    ((prod.fst : A' ⨯ B' ⟶ A').app n).app X (((prod.map f g).app n).app X z) =
      (f.app n).app X (((prod.fst : A ⨯ B ⟶ A).app n).app X z) := by
  have := congrArg (fun φ => (φ.app n).app X z) (prod.map_fst f g)
  simp only [NatTrans.comp_app] at this
  exact this

theorem map_snd_app {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ)
    (z : ((A ⨯ B).obj n).obj X) :
    ((prod.snd : A' ⨯ B' ⟶ B').app n).app X (((prod.map f g).app n).app X z) =
      (g.app n).app X (((prod.snd : A ⨯ B ⟶ B).app n).app X z) := by
  have := congrArg (fun φ => (φ.app n).app X z) (prod.map_snd f g)
  simp only [NatTrans.comp_app] at this
  exact this

theorem prod_ext_app {A B : Spc} (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ) (z w : ((A ⨯ B).obj n).obj X)
    (h1 : ((prod.fst : A ⨯ B ⟶ A).app n).app X z = ((prod.fst : A ⨯ B ⟶ A).app n).app X w)
    (h2 : ((prod.snd : A ⨯ B ⟶ B).app n).app X z = ((prod.snd : A ⨯ B ⟶ B).app n).app X w) : z = w :=
  (prod_elt_bij A B n X).1 (Prod.ext h1 h2)

theorem LeafWLoc_of : LeafWLoc := by
  intro d R _ n X x
  let c : ComposableArrows (Vec (d + 1) 0 X) n.unop.len :=
    ((prod.fst : PR (d + 1) 0 R ⟶ Pj (d + 1) 0).app n).app (op X) x
  let s := ((prod.snd : PR (d + 1) 0 R ⟶ sp R).app n).app (op X) x
  refine ⟨Fin (d + 1), fun j => X.basicOpen ((c.obj 0).1 j), ?_, fun j => ?_⟩
  · refine eq_top_iff.2 fun p _ => ?_
    obtain ⟨j, -, hj⟩ := (c.obj 0).2 p
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩
  · let O := X.basicOpen ((c.obj 0).1 j)
    let cr : ComposableArrows (Vec (d + 1) 0 O) n.unop.len := c ⋙ Vec.map (d + 1) 0 O.ι
    let sr := ((sp R).obj n).map O.ι.op s
    have hbo : ∀ a i (p : (O : Scheme.{0})), p ∈ (O : Scheme.{0}).basicOpen ((cr.obj a).1 i) ↔
        p.val ∈ X.basicOpen ((c.obj 0).1 i) := fun a i p => by
      rw [← bo_chain c a i]; exact mem_bo_map O (c.obj a) i p
    by_cases hj : j = 0
    · left
      obtain ⟨y, hy⟩ := (prod_elt_bij (Wsp d) (sp R) n (op (O : Scheme.{0}))).2
        (liftW cr (fun a => isUnit_of_bo _ fun p => (hbo a 0 p).2 (hj ▸ p.2)), sr)
      refine ⟨y, prod_ext_app _ _ _ _ ?_ ?_⟩
      · change ((prod.fst : PR (d + 1) 0 R ⟶ _).app n).app _ (((prod.map (Wincl d) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_fst_app, fst_map]
        refine (congrArg (fun w => ((Wincl d).app n).app _ w) (congrArg Prod.fst hy)).trans ?_
        rfl
      · change ((prod.snd : PR (d + 1) 0 R ⟶ _).app n).app _ (((prod.map (Wincl d) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_snd_app, snd_map]
        refine (congrArg (fun w => ((𝟙 (sp R) : sp R ⟶ sp R).app n).app _ w) (congrArg Prod.snd hy)).trans ?_
        rfl
    · right
      have hj1 : 1 ≤ j.val := Nat.one_le_iff_ne_zero.2 fun h => hj (Fin.ext h)
      obtain ⟨y, hy⟩ := (prod_elt_bij (Pj (d + 1) 1) (sp R) n (op (O : Scheme.{0}))).2
        (lift1 cr (fun a p => ⟨j, hj1, (hbo a j p).2 p.2⟩), sr)
      refine ⟨y, prod_ext_app _ _ _ _ ?_ ?_⟩
      · change ((prod.fst : PR (d + 1) 0 R ⟶ _).app n).app _
          (((prod.map (Pj.incl (d + 1)) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_fst_app, fst_map]
        refine (congrArg (fun w => ((Pj.incl (d + 1)).app n).app _ w) (congrArg Prod.fst hy)).trans ?_
        rfl
      · change ((prod.snd : PR (d + 1) 0 R ⟶ _).app n).app _
          (((prod.map (Pj.incl (d + 1)) (𝟙 (sp R))).app n).app _ y) = _
        rw [map_snd_app, snd_map]
        refine (congrArg (fun w => ((𝟙 (sp R) : sp R ⟶ sp R).app n).app _ w) (congrArg Prod.snd hy)).trans ?_
        rfl

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
