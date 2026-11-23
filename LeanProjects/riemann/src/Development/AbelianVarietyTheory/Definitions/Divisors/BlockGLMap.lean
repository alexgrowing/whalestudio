import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

def ofCatMap {C D : CommRingCat.{0} ⥤ Cat.{0,0}} (α : C ⟶ D) : ofCat C ⟶ ofCat D :=
  (flipFunctor _ _ _).map (Functor.whiskerLeft Scheme.Γ (Functor.whiskerRight α nerveFunctor))

def Um (N : ℕ) (A : Type) [CommRing A] : Type := {v : Fin N → A // Ideal.span (Set.range v) = ⊤}

instance (N : ℕ) (A : Type) [CommRing A] : SmallCategory (Um N A) where
  Hom v w := {p : GL (Fin N) A × Aˣ // (p.1 : Matrix _ _ A).mulVec v.1 = (p.2 : A) • w.1}
  id v := ⟨1, by simp⟩
  comp f g := ⟨g.1 * f.1, by
    rw [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, f.2, Matrix.mulVec_smul, g.2,
      smul_smul, mul_comm]⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

def Um.map (N : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : Um N A ⥤ Um N B where
  obj v := ⟨f ∘ v.1, by rw [Set.range_comp, ← Ideal.map_span, v.2, Ideal.map_top]⟩
  map {v w} p := ⟨(Matrix.GeneralLinearGroup.map f p.1.1, Units.map (f : A →* B) p.1.2), by
    funext i
    have h := congrArg f (congrFun p.2 i)
    rw [RingHom.map_mulVec] at h
    simpa using h⟩
  map_id v := Subtype.ext (Prod.ext (map_one (Matrix.GeneralLinearGroup.map f)) (map_one (Units.map (f : A →* B))))
  map_comp p q := Subtype.ext (Prod.ext (map_mul (Matrix.GeneralLinearGroup.map f) _ _) (map_mul (Units.map (f : A →* B)) _ _))

def pglCat (N : ℕ) : CommRingCat.{0} ⥤ Cat.{0,0} where
  obj A := Cat.of (Um N A)
  map f := (Um.map N f.hom).toCatHom
  map_id A := rfl
  map_comp f g := rfl

abbrev BGL (N : ℕ) (S : Scheme.{0}) : Spc := ofCat (glCat N) ⨯ sch.obj S

def PGL (N : ℕ) : Spc := ofCat (pglCat N)

def Um.toGL (N : ℕ) (A : Type) [CommRing A] : Um N A ⥤ SingleObj (GL (Fin N) A) where
  obj _ := SingleObj.star _
  map p := p.1.1
  map_id _ := rfl
  map_comp _ _ := rfl

def Um.toLine (N : ℕ) (A : Type) [CommRing A] : Um N A ⥤ SingleObj (GL (Fin 1) A) where
  obj _ := SingleObj.star _
  map p := Matrix.GeneralLinearGroup.scalar (Fin 1) p.1.2
  map_id _ := map_one (Matrix.GeneralLinearGroup.scalar (Fin 1))
  map_comp _ _ := map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _

def PGL.pr (N : ℕ) : PGL N ⟶ ofCat (glCat N) :=
  ofCatMap { app := fun A => (Um.toGL N A).toCatHom, naturality := fun _ _ _ => rfl }

def PGL.line (N : ℕ) : PGL N ⟶ ofCat (glCat 1) :=
  ofCatMap
    { app := fun A => (Um.toLine N A).toCatHom
      naturality := fun A B f => by
        apply Cat.Hom.ext
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
        change Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map (f.hom : A →* B) p.1.2) =
          Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) p.1.2)
        ext i j
        obtain rfl : i = j := Subsingleton.elim _ _
        simp }

def prodCat (C D : CommRingCat.{0} ⥤ Cat.{0,0}) : CommRingCat.{0} ⥤ Cat.{0,0} where
  obj A := Cat.of (C.obj A × D.obj A)
  map f := ((C.map f).toFunctor.prod (D.map f).toFunctor).toCatHom
  map_id A := by rw [C.map_id, D.map_id]; rfl
  map_comp f g := by rw [C.map_comp, D.map_comp]; rfl

def liftCat {E : Spc} {C D : CommRingCat.{0} ⥤ Cat.{0,0}} (V : E ⟶ ofCat C) (W : E ⟶ ofCat D) : E ⟶ ofCat (prodCat C D) where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        Functor.prod' (show Fin (n.unop.len + 1) ⥤ C.obj (Scheme.Γ.obj U) from (V.app n).app U x)
          (show Fin (n.unop.len + 1) ⥤ D.obj (Scheme.Γ.obj U) from (W.app n).app U x)
      naturality := fun U U' f => by
        ext x
        have h1 := ConcreteCategory.congr_hom ((V.app n).naturality f) x
        have h2 := ConcreteCategory.congr_hom ((W.app n).naturality f) x
        exact congrArg₂ Functor.prod' h1 h2 }
  naturality n m f := by
    ext U x
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (V.naturality f) U) x
    have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (W.naturality f) U) x
    exact congrArg₂ Functor.prod' h1 h2

def blockMat (a b : ℕ) (A : Type) [CommRing A] :
    Matrix (Fin a) (Fin a) A × Matrix (Fin b) (Fin b) A →* Matrix (Fin (a + b)) (Fin (a + b)) A where
  toFun p := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]

def blockGL (a b : ℕ) (A : Type) [CommRing A] (g : GL (Fin a) A) (h : GL (Fin b) A) : GL (Fin (a + b)) A :=
  Units.map (blockMat a b A) (MulEquiv.prodUnits.symm (g, h))

theorem blockGL_val (a b : ℕ) (A : Type) [CommRing A] (g : GL (Fin a) A) (h : GL (Fin b) A) :
    Units.val (blockGL a b A g h) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.val 0 0 h.val) := rfl

open CategoryTheory Limits AlgebraicGeometry Opposite in
theorem _root_.GlobalTheory.EtC.blockGL_map (a b : ℕ) {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (g : GL (Fin a) A) (h : GL (Fin b) A) :
    _root_.GlobalTheory.EtC.blockGL a b B (Matrix.GeneralLinearGroup.map f g)
        (Matrix.GeneralLinearGroup.map f h) =
      Matrix.GeneralLinearGroup.map f (_root_.GlobalTheory.EtC.blockGL a b A g h) := by
  ext i j
  simp only [_root_.GlobalTheory.EtC.blockGL_val, Matrix.GeneralLinearGroup.map_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

def blockFun (a b : ℕ) (A : Type) [CommRing A] :
    SingleObj (GL (Fin a) A) × SingleObj (GL (Fin b) A) ⥤ SingleObj (GL (Fin (a + b)) A) where
  obj _ := SingleObj.star _
  map p := blockGL a b A p.1 p.2
  map_id _ := Units.ext (map_one (blockMat a b A))
  map_comp f g := Units.ext (map_mul (blockMat a b A) (Units.val (show GL (Fin a) A from g.1), Units.val (show GL (Fin b) A from g.2))
    (Units.val (show GL (Fin a) A from f.1), Units.val (show GL (Fin b) A from f.2)))

def blockNat (a b : ℕ) : prodCat (glCat a) (glCat b) ⟶ glCat (a + b) where
  app A := (blockFun a b A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
    exact blockGL_map a b f.hom p.1 p.2

def bsumOf {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) : E ⟶ ofCat (glCat (a + b)) :=
  liftCat V W ≫ ofCatMap (blockNat a b)

def bsum (a b : ℕ) : ofCat (glCat a) ⨯ ofCat (glCat b) ⟶ ofCat (glCat (a + b)) := bsumOf prod.fst prod.snd

def tautOf {E : Spc} (C : CommRingCat.{0} ⥤ Cat.{0,0}) (A : CommRingCat.{0}) (V : E ⟶ cst (C.obj A)) (s : E ⟶ sch.obj (Spec A)) :
    E ⟶ ofCat C where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        (show Fin (n.unop.len + 1) ⥤ C.obj A from (V.app n).app U x) ⋙
          (C.map ((Scheme.ΓSpecIso A).inv ≫ (show U.unop ⟶ Spec A from (s.app n).app U x).appTop)).toFunctor
      naturality := fun U U' f => by
        ext x
        have h1 : (V.app n).app U' ((E.obj n).map f x) = (V.app n).app U x :=
          ConcreteCategory.congr_hom ((V.app n).naturality f) x
        have h2 : (s.app n).app U' ((E.obj n).map f x) = f.unop ≫ (show U.unop ⟶ Spec A from (s.app n).app U x) :=
          ConcreteCategory.congr_hom ((s.app n).naturality f) x
        change (show Fin (n.unop.len + 1) ⥤ C.obj A from (V.app n).app U' ((E.obj n).map f x)) ⋙
          (C.map ((Scheme.ΓSpecIso A).inv ≫ (show U'.unop ⟶ Spec A from (s.app n).app U' ((E.obj n).map f x)).appTop)).toFunctor =
          ((show Fin (n.unop.len + 1) ⥤ C.obj A from (V.app n).app U x) ⋙
          (C.map ((Scheme.ΓSpecIso A).inv ≫ (show U.unop ⟶ Spec A from (s.app n).app U x).appTop)).toFunctor) ⋙
            (C.map f.unop.appTop).toFunctor
        rw [h1, h2, Scheme.Hom.comp_appTop, ← Category.assoc, C.map_comp]
        rfl }
  naturality n m f := by
    ext U x
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (V.naturality f) U) x
    have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (s.naturality f) U) x
    exact congrArg₂ (fun (y : Fin (m.unop.len + 1) ⥤ C.obj A) (t : U.unop ⟶ Spec A) =>
      y ⋙ (C.map ((Scheme.ΓSpecIso A).inv ≫ t.appTop)).toFunctor) h1 h2

def taut (N : ℕ) (A : Type) [CommRing A] : cst (SingleObj (GL (Fin N) A)) ⨯ sp A ⟶ ofCat (glCat N) :=
  tautOf (glCat N) (CommRingCat.of A) prod.fst prod.snd

def grpSimplex {Γ : Type} [Group Γ] {m : ℕ} (g : Fin m → Γ) : ComposableArrows (SingleObj Γ) m :=
  ComposableArrows.mkOfObjOfMapSucc (fun _ => SingleObj.star Γ) (fun i => (g i)⁻¹)

def grpPt {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (g : Fin m → Γ) :
    yoneda.obj X ⟶ (cst (SingleObj Γ) ⨯ sch.obj X).obj (op (SimplexCategory.mk m)) :=
  haveI : PreservesLimit (pair (cst (SingleObj Γ)) (sch.obj X))
      ((evaluation SimplexCategoryᵒᵖ (Scheme.{0}ᵒᵖ ⥤ Type)).obj (op (SimplexCategory.mk m))) :=
    (evaluation_preservesLimitsOfShape (J := Discrete WalkingPair) _).preservesLimit
  prod.lift
    ({ app := fun U => TypeCat.ofHom fun _ => grpSimplex g, naturality := fun _ _ _ => rfl } :
      yoneda.obj X ⟶ (cst (SingleObj Γ)).obj (op (SimplexCategory.mk m))) (𝟙 (yoneda.obj X)) ≫
    (PreservesLimitPair.iso ((evaluation _ _).obj (op (SimplexCategory.mk m))) (cst (SingleObj Γ)) (sch.obj X)).inv

def IsSlant (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R)
    (z : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) ((chains R).obj (cst (SingleObj Γ) ⨯ sch.obj X)) (-(m : ℤ))) :
    Prop :=
  (∀ (p p' : ℤ) (h : p + -(m : ℤ) = p'), p ≠ 0 → z.1.v p p' h = 0) ∧
  z.1.v 0 (-(m : ℤ)) (zero_add _) =
    (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        (((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj X))).extendXIso
        ComplexShape.embeddingDownNat (i := 0) (i' := 0) (by simp)).hom ≫
      (c.sum fun g r => (ULift.up r : ULift.{1} R) • (free R).map (grpPt X g)) ≫
      (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        (((SimplicialObject.whiskering _ _).obj (free R)).obj (cst (SingleObj Γ) ⨯ sch.obj X))).extendXIso
        ComplexShape.embeddingDownNat (i := m) (i' := -(m : ℤ)) (by simp)).inv

def IsSlantMap (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (F : Shv R) (m : ℕ) (n : ℤ)
    (S : groupHomology (Rep.trivial R Γ R) m →+ H R (cst (SingleObj Γ) ⨯ sch.obj X) F (m + n) →+ H R (sch.obj X) F n) : Prop :=
  ∀ (c : groupHomology.cycles (Rep.trivial R Γ R) m) z, IsSlant R X (groupHomology.iCycles (Rep.trivial R Γ R) m c) z →
    S (groupHomology.π (Rep.trivial R Γ R) m c) = HK.pre R z F (m + n) n (by ring)

open Classical in

def slantR (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (F : Shv R) (m : ℕ) (n : ℤ) :
    groupHomology (Rep.trivial R Γ R) m →+ H R (cst (SingleObj Γ) ⨯ sch.obj X) F (m + n) →+ H R (sch.obj X) F n :=
  if h : ∃ S, IsSlantMap R Γ X F m n S then h.choose else 0

abbrev slant (q : ℕ) (Γ : Type) [Group Γ] (X : Scheme.{0}) (F : Shv (ZMod q)) (m : ℕ) (n : ℤ) :
    groupHomology (Rep.trivial (ZMod q) Γ (ZMod q)) m →+
      H (ZMod q) (cst (SingleObj Γ) ⨯ sch.obj X) F (m + n) →+ H (ZMod q) (sch.obj X) F n :=
  slantR (ZMod q) Γ X F m n

end GlobalTheory.EtC

end
