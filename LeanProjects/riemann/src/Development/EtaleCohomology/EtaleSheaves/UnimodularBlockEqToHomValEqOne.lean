import Development.EtaleCohomology.EtaleSheaves.LeafGeomPfLoc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.LeafHalf1Pf

theorem pbSq {A B C : Spc} (f : A ⟶ C) (g : B ⟶ C) (n : ℕ) (X : Scheme.{0}) :
    IsPullback (((pullback.fst f g).app (op (SimplexCategory.mk n))).app (op X))
      (((pullback.snd f g).app (op (SimplexCategory.mk n))).app (op X))
      ((f.app (op (SimplexCategory.mk n))).app (op X)) ((g.app (op (SimplexCategory.mk n))).app (op X)) := by
  have h1 := (IsPullback.of_hasPullback f g).map ((evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk n)))
  exact h1.map ((evaluation Scheme.{0}ᵒᵖ Type).obj (op X))

theorem pb_ext {A B C : Spc} {f : A ⟶ C} {g : B ⟶ C} {n : ℕ} {X : Scheme.{0}} {z w : Sx (pullback f g) n X}
    (h1 : ((pullback.fst f g).app _).app _ z = ((pullback.fst f g).app _).app _ w)
    (h2 : ((pullback.snd f g).app _).app _ z = ((pullback.snd f g).app _).app _ w) : z = w :=
  Types.ext_of_isPullback (pbSq f g n X) h1 h2

theorem pb_exists {A B C : Spc} (f : A ⟶ C) (g : B ⟶ C) {n : ℕ} {X : Scheme.{0}} (a : Sx A n X) (b : Sx B n X)
    (h : (f.app _).app _ a = (g.app _).app _ b) :
    ∃ z : Sx (pullback f g) n X, ((pullback.fst f g).app _).app _ z = a ∧ ((pullback.snd f g).app _).app _ z = b :=
  Types.exists_of_isPullback (pbSq f g n X) a b h

def bl (a b : ℕ) (A : Type) [CommRing A] : GL (Fin a) A × GL (Fin b) A →* GL (Fin (a + b)) A :=
  (Units.map (blockMat a b A)).comp (MulEquiv.prodUnits.symm : GL (Fin a) A × GL (Fin b) A ≃* _).toMonoidHom

theorem blockDiagonal_apply₂ (a b : ℕ) (A : Type) [CommRing A] (p : GL (Fin a) A × GL (Fin b) A) : bl a b A p = blockGL a b A p.1 p.2 := rfl

theorem blockDiagonal_mulVec_castAdd {a b : ℕ} {A : Type} [CommRing A] (p : GL (Fin a) A × GL (Fin b) A) (v : Fin (a + b) → A) (i : Fin a) :
    ((bl a b A p : GL (Fin (a + b)) A) : Matrix _ _ A).mulVec v (Fin.castAdd b i) =
      ((p.1 : Matrix _ _ A).mulVec (fun j => v (Fin.castAdd b j))) i := by
  rw [blockDiagonal_apply₂, blockGL_val]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.reindex_apply]

theorem span_mulVec_le {m k : ℕ} {A : Type} [CommRing A] (M : Matrix (Fin m) (Fin k) A) (v : Fin k → A) :
    Ideal.span (Set.range (M.mulVec v)) ≤ Ideal.span (Set.range v) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  show ∑ j, M i j * v j ∈ _
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem span_smul_le {k : ℕ} {A : Type} [CommRing A] (c : A) (v : Fin k → A) :
    Ideal.span (Set.range (c • v)) ≤ Ideal.span (Set.range v) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

def U1 (a b : ℕ) (A : Type) [CommRing A] : Type :=
  {v : Um (a + b) A // Ideal.span (Set.range fun i : Fin a => v.1 (Fin.castAdd b i)) = ⊤}

instance (a b : ℕ) (A : Type) [CommRing A] : SmallCategory (U1 a b A) where
  Hom v w := {p : (GL (Fin a) A × GL (Fin b) A) × Aˣ //
    ((bl a b A p.1 : GL (Fin (a + b)) A) : Matrix _ _ A).mulVec v.1.1 = (p.2 : A) • w.1.1}
  id v := ⟨1, by simp⟩
  comp f g := ⟨g.1 * f.1, by
    rw [Prod.fst_mul, Prod.snd_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, f.2, Matrix.mulVec_smul, g.2,
      smul_smul, mul_comm]⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

theorem unimodularBlock_comp_val_eq_mul {a b : ℕ} {A : Type} [CommRing A] {u v w : U1 a b A} (f : u ⟶ v) (g : v ⟶ w) : (f ≫ g).1 = g.1 * f.1 := rfl

theorem unimodularBlock_eqToHom_val_eq_one {a b : ℕ} {A : Type} [CommRing A] {v w : U1 a b A} (h : v = w) : (eqToHom h).1 = 1 := by
  subst h; rfl

theorem Um_comp_val {N : ℕ} {A : Type} [CommRing A] {u v w : Um N A} (f : u ⟶ v) (g : v ⟶ w) : (f ≫ g).1 = g.1 * f.1 := rfl

theorem Um_eqToHom_val {N : ℕ} {A : Type} [CommRing A] {v w : Um N A} (h : v = w) : (eqToHom h).1 = 1 := by
  subst h; rfl

theorem Um_comp_eqToHom {N : ℕ} {A : Type} [CommRing A] {u v w : Um N A} (p : u ⟶ v) (h : v = w) :
    (p ≫ eqToHom h).1 = p.1 := by
  subst h; simp

theorem Um_eqToHom_comp {N : ℕ} {A : Type} [CommRing A] {u v w : Um N A} (h : u = v) (p : v ⟶ w) :
    (eqToHom h ≫ p).1 = p.1 := by
  subst h; simp

def unimodularBlockCategoryMapRingHom (a b : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : U1 a b A ⥤ U1 a b B where
  obj v := ⟨(Um.map (a + b) f).obj v.1, by
    show Ideal.span (Set.range (f ∘ fun i : Fin a => v.1.1 (Fin.castAdd b i))) = ⊤
    rw [Set.range_comp, ← Ideal.map_span, v.2, Ideal.map_top]⟩
  map {v w} p := ⟨((Matrix.GeneralLinearGroup.map f p.1.1.1, Matrix.GeneralLinearGroup.map f p.1.1.2), Units.map (f : A →* B) p.1.2), by
    have e : bl a b B (Matrix.GeneralLinearGroup.map f p.1.1.1, Matrix.GeneralLinearGroup.map f p.1.1.2) =
        Matrix.GeneralLinearGroup.map f (bl a b A p.1.1) := blockGL_map a b f _ _
    rw [e]
    funext i
    have h := congrArg f (congrFun p.2 i)
    rw [RingHom.map_mulVec] at h
    simpa [Um.map] using h⟩
  map_id v := Subtype.ext (Prod.ext (Prod.ext (map_one _) (map_one _)) (map_one _))
  map_comp p q := Subtype.ext (Prod.ext (Prod.ext (map_mul _ _ _) (map_mul _ _ _)) (map_mul _ _ _))

def cat1 (a b : ℕ) : CommRingCat.{0} ⥤ Cat.{0,0} where
  obj A := Cat.of (U1 a b A)
  map f := (unimodularBlockCategoryMapRingHom a b f.hom).toCatHom
  map_id A := rfl
  map_comp f g := rfl

def toProd (a b : ℕ) (A : Type) [CommRing A] : U1 a b A ⥤ SingleObj (GL (Fin a) A) × SingleObj (GL (Fin b) A) where
  obj _ := (SingleObj.star _, SingleObj.star _)
  map p := (p.1.1.1, p.1.1.2)
  map_id _ := rfl
  map_comp _ _ := rfl

def toUm (a b : ℕ) (A : Type) [CommRing A] : U1 a b A ⥤ Um (a + b) A where
  obj v := v.1
  map p := ⟨(bl a b A p.1.1, p.1.2), p.2⟩
  map_id _ := Subtype.ext (Prod.ext (map_one _) rfl)
  map_comp _ _ := Subtype.ext (Prod.ext (map_mul _ _ _) rfl)

def toFirst (a b : ℕ) (A : Type) [CommRing A] : U1 a b A ⥤ Um a A where
  obj v := ⟨fun i => v.1.1 (Fin.castAdd b i), v.2⟩
  map {v w} p := ⟨(p.1.1.1, p.1.2), by
    funext i
    have h := congrFun p.2 (Fin.castAdd b i)
    rw [blockDiagonal_mulVec_castAdd] at h
    simpa using h⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def pr1 (a b : ℕ) : cat1 a b ⟶ prodCat (glCat a) (glCat b) where
  app A := (toProd a b A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => HEq.rfl)

def sig (a b : ℕ) : cat1 a b ⟶ pglCat (a + b) where
  app A := (toUm a b A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
    first
    | exact Subtype.ext (Prod.ext (blockGL_map a b f.hom p.1.1.1 p.1.1.2).symm rfl)
    | exact Subtype.ext (Prod.ext (blockGL_map a b f.hom p.1.1.1 p.1.1.2) rfl)
    | exact Prod.ext (blockGL_map a b f.hom p.1.1.1 p.1.1.2).symm rfl
    | exact Prod.ext (blockGL_map a b f.hom p.1.1.1 p.1.1.2) rfl

def rho (a b : ℕ) : cat1 a b ⟶ pglCat a where
  app A := (toFirst a b A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => HEq.rfl)

def fstNat (C D : CommRingCat.{0} ⥤ Cat.{0,0}) : prodCat C D ⟶ C where
  app A := (CategoryTheory.Prod.fst (C.obj A) (D.obj A)).toCatHom
  naturality A B f := rfl

def glNat (N : ℕ) : pglCat N ⟶ glCat N := { app := fun A => (Um.toGL N A).toCatHom, naturality := fun _ _ _ => rfl }

theorem ofCatMap_comp {C D F : CommRingCat.{0} ⥤ Cat.{0,0}} (α : C ⟶ D) (β : D ⟶ F) :
    ofCatMap (α ≫ β) = ofCatMap α ≫ ofCatMap β := by
  first
  | rfl
  | (unfold ofCatMap; rw [Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Functor.map_comp])
  | simp [ofCatMap]

theorem liftCat_fst {E : Spc} {C D : CommRingCat.{0} ⥤ Cat.{0,0}} (V : E ⟶ ofCat C) (W : E ⟶ ofCat D) :
    liftCat V W ≫ ofCatMap (fstNat C D) = V := by
  first
  | rfl
  | (ext n U x; rfl)
  | (ext n U x; exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => by simp))

theorem e_rho (a b : ℕ) : rho a b ≫ glNat a = pr1 a b ≫ fstNat _ _ := by
  ext A
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => HEq.rfl)

theorem e_sig (a b : ℕ) : sig a b ≫ glNat (a + b) = pr1 a b ≫ blockNat a b := by
  ext A
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => HEq.rfl)

def lineNat (N : ℕ) : pglCat N ⟶ glCat 1 where
  app A := (Um.toLine N A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
    change Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map (f.hom : A →* B) p.1.2) =
      Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) p.1.2)
    ext i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp

theorem e_line (a b : ℕ) : rho a b ≫ lineNat a = sig a b ≫ lineNat (a + b) := by
  ext A
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => HEq.rfl)

theorem first_transfer {a : ℕ} {A : Type} [CommRing A] (g : GL (Fin a) A) (u : Aˣ) (v0 vi : Fin a → A)
    (h : Matrix.mulVec (g : Matrix (Fin a) (Fin a) A) v0 = (u : A) • vi) (h0 : Ideal.span (Set.range v0) = ⊤) : Ideal.span (Set.range vi) = ⊤ := by
  rw [eq_top_iff, ← h0]
  have e : v0 = Matrix.mulVec ((g⁻¹ : GL (Fin a) A) : Matrix (Fin a) (Fin a) A) (Matrix.mulVec (g : Matrix (Fin a) (Fin a) A) v0) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [e, h]
  exact (span_mulVec_le _ _).trans (span_smul_le _ _)

theorem eqToHom_ps {M N : Type} [Monoid M] [Monoid N] {x y : SingleObj M × SingleObj N} (h : x = y) :
    eqToHom h = (show x ⟶ y from ((1 : M), (1 : N))) := by
  cases h; rfl

theorem jmF {a b : ℕ} {A : Type} [CommRing A] {J : Type} [Category J] (F G : J ⥤ U1 a b A)
    (h1 : F ⋙ toUm a b A = G ⋙ toUm a b A) (h2 : F ⋙ toProd a b A = G ⋙ toProd a b A) : F = G := by
  have ho : ∀ i, F.obj i = G.obj i := fun i => Subtype.ext (CategoryTheory.Functor.congr_obj h1 i)
  refine CategoryTheory.Functor.ext ho (fun i j f => ?_)
  apply Subtype.ext
  rw [unimodularBlock_comp_val_eq_mul, unimodularBlock_comp_val_eq_mul, unimodularBlock_eqToHom_val_eq_one, unimodularBlock_eqToHom_val_eq_one]
  simp only [one_mul, mul_one]
  have k1 := congrArg (fun q => q.1) (CategoryTheory.Functor.congr_hom h1 f)
  first
  | (rw [Um_eqToHom_comp, Um_comp_eqToHom] at k1)
  | (simp only [Um_eqToHom_comp, Um_comp_eqToHom] at k1)
  | (rw [Um_comp_val, Um_comp_val, Um_eqToHom_val, Um_eqToHom_val] at k1; simp only [one_mul, mul_one] at k1)
  have ku : (F.map f).1.2 = (G.map f).1.2 := by
    have := congrArg Prod.snd k1
    exact this
  have k2 := CategoryTheory.Functor.congr_hom h2 f
  rw [eqToHom_ps, eqToHom_ps] at k2
  have kg : (F.map f).1.1.1 = (1 * (G.map f).1.1.1) * 1 := congrArg Prod.fst k2
  have kh : (F.map f).1.1.2 = (1 * (G.map f).1.1.2) * 1 := congrArg Prod.snd k2
  simp only [one_mul, mul_one] at kg kh
  exact Prod.ext (Prod.ext kg kh) ku

theorem JM {T : Spc} {a b : ℕ} (s t : T ⟶ ofCat (cat1 a b)) (h1 : s ≫ ofCatMap (sig a b) = t ≫ ofCatMap (sig a b))
    (h2 : s ≫ ofCatMap (pr1 a b) = t ≫ ofCatMap (pr1 a b)) : s = t := by
  ext n U x
  have e1 := congrArg (fun φ : T ⟶ _ => (φ.app n).app U x) h1
  have e2 := congrArg (fun φ : T ⟶ _ => (φ.app n).app U x) h2
  exact jmF (J := Fin (n.unop.len + 1)) (A := ↑(Scheme.Γ.obj U)) ((s.app n).app U x) ((t.app n).app U x) e1 e2

theorem singleObj_eqToHom_eq_monoid_one {M : Type} [Monoid M] {x y : SingleObj M} (h : x = y) : eqToHom h = (show x ⟶ y from (1 : M)) := by
  cases h; rfl

def sigP (a b : ℕ) : ofCat (cat1 a b) ⟶ PGL (a + b) := ofCatMap (sig a b)
def rhoP (a b : ℕ) : ofCat (cat1 a b) ⟶ PGL a := ofCatMap (rho a b)

theorem sigP_pr (a b : ℕ) : sigP a b ≫ PGL.pr (a + b) = ofCatMap (pr1 a b) ≫ ofCatMap (blockNat a b) :=
  (ofCatMap_comp _ _).symm.trans ((congrArg ofCatMap (e_sig a b)).trans (ofCatMap_comp _ _))

theorem rhoP_pr (a b : ℕ) : rhoP a b ≫ PGL.pr a = ofCatMap (pr1 a b) ≫ ofCatMap (fstNat _ _) :=
  (ofCatMap_comp _ _).symm.trans ((congrArg ofCatMap (e_rho a b)).trans (ofCatMap_comp _ _))

theorem rhoP_line (a b : ℕ) : rhoP a b ≫ PGL.line a = sigP a b ≫ PGL.line (a + b) :=
  (ofCatMap_comp _ _).symm.trans ((congrArg ofCatMap (e_line a b)).trans (ofCatMap_comp _ _))

theorem LeafHalf1_of : LeafHalf1 := by
  intro E a b V W
  have hp : pullback.fst (liftCat V W) (ofCatMap (pr1 a b)) ≫ V =
      (pullback.snd (liftCat V W) (ofCatMap (pr1 a b)) ≫ rhoP a b) ≫ PGL.pr a := by
    rw [Category.assoc, rhoP_pr, ← Category.assoc, ← pullback.condition, Category.assoc, liftCat_fst]
  have hf : pullback.fst (liftCat V W) (ofCatMap (pr1 a b)) ≫ bsumOf V W =
      (pullback.snd (liftCat V W) (ofCatMap (pr1 a b)) ≫ sigP a b) ≫ PGL.pr (a + b) := by
    rw [Category.assoc, sigP_pr, ← Category.assoc, ← pullback.condition, Category.assoc]
    rfl
  refine ⟨pullback (liftCat V W) (ofCatMap (pr1 a b)), pullback.lift _ _ hf, pullback.lift _ _ hp, ⟨fun {T} g1 g2 h => ?_⟩, ?_, ?_, ?_⟩
  · have ef := pullback.lift_fst (f := bsumOf V W) (g := PGL.pr (a + b)) _ _ hf
    have es := pullback.lift_snd (f := bsumOf V W) (g := PGL.pr (a + b)) _ _ hf
    have h1 : g1 ≫ pullback.fst _ _ = g2 ≫ pullback.fst _ _ :=
      (congrArg (g1 ≫ ·) ef.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.fst (bsumOf V W) (PGL.pr (a + b))) h).trans ((Category.assoc _ _ _).trans (congrArg (g2 ≫ ·) ef))))
    have h2 : (g1 ≫ pullback.snd _ _) ≫ sigP a b = (g2 ≫ pullback.snd _ _) ≫ sigP a b :=
      (Category.assoc _ _ _).trans ((congrArg (g1 ≫ ·) es.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.snd (bsumOf V W) (PGL.pr (a + b))) h).trans ((Category.assoc _ _ _).trans
          ((congrArg (g2 ≫ ·) es).trans (Category.assoc _ _ _).symm)))))
    have h3 : (g1 ≫ pullback.snd _ _) ≫ ofCatMap (pr1 a b) = (g2 ≫ pullback.snd _ _) ≫ ofCatMap (pr1 a b) := by
      rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc, ← Category.assoc, h1]
    exact pullback.hom_ext h1 (JM _ _ h2 h3)
  · exact (pullback.lift_fst _ _ hp).trans (pullback.lift_fst _ _ hf).symm
  · dsimp only [PB.line]
    rw [← Category.assoc, ← Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, Category.assoc, rhoP_line]
  · intro n X x hF
    let e := ((pullback.fst (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x
    let F : Fin (n + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X)) :=
      ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x
    let Ve : Fin (n + 1) ⥤ SingleObj (GL (Fin a) (Scheme.Γ.obj (op X))) := (V.app (op (SimplexCategory.mk n))).app (op X) e
    let We : Fin (n + 1) ⥤ SingleObj (GL (Fin b) (Scheme.Γ.obj (op X))) := (W.app (op (SimplexCategory.mk n))).app (op X) e
    have cond : Functor.prod' Ve We ⋙ blockFun a b _ = F ⋙ Um.toGL (a + b) _ :=
      congrArg (fun φ : PB (bsumOf V W) ⟶ ofCat (glCat (a + b)) => (φ.app (op (SimplexCategory.mk n))).app (op X) x)
        (pullback.condition (f := bsumOf V W) (g := PGL.pr (a + b)))
    have hb : ∀ {i j : Fin (n + 1)} (f : i ⟶ j), bl a b _ (Ve.map f, We.map f) = (F.map f).1.1 := by
      intro i j f
      have := CategoryTheory.Functor.congr_hom cond f
      simp only [singleObj_eqToHom_eq_monoid_one] at this
      have t : blockGL a b _ (Ve.map f) (We.map f) = (1 * (F.map f).1.1) * 1 := this
      rw [blockDiagonal_apply₂]
      first
      | exact t.trans (by simp only [mul_one, one_mul])
      | exact t.trans (by rw [mul_one, one_mul])
      | exact t.trans ((congrArg (· * 1) (one_mul _)).trans (mul_one _))
    have hfirst : ∀ i, Ideal.span (Set.range fun k : Fin a => (F.obj i).1 (Fin.castAdd b k)) = ⊤ := by
      intro i
      let f0 : (0 : Fin (n + 1)) ⟶ i := homOfLE (Fin.zero_le i)
      have h0 : Ideal.span (Set.range fun k : Fin a => (F.obj 0).1 (Fin.castAdd b k)) = ⊤ := hF
      refine first_transfer (show GL (Fin a) _ from Ve.map f0) (F.map f0).1.2 _ _ ?_ h0
      funext k
      have h := congrFun (F.map f0).2 (Fin.castAdd b k)
      rw [← hb f0, blockDiagonal_mulVec_castAdd] at h
      exact h
    let G : Fin (n + 1) ⥤ U1 a b (Scheme.Γ.obj (op X)) :=
      { obj := fun i => ⟨F.obj i, hfirst i⟩
        map := fun {i j} f => ⟨((Ve.map f, We.map f), (F.map f).1.2), by
          show Matrix.mulVec ((bl a b _ (Ve.map f, We.map f) : GL _ _) : Matrix _ _ _) (F.obj i).1 = ((F.map f).1.2 : _) • (F.obj j).1
          rw [hb f]
          exact (F.map f).2⟩
        map_id := fun i => Subtype.ext (Prod.ext (Prod.ext (Ve.map_id i) (We.map_id i)) (congrArg (fun q => q.1.2) (F.map_id i)))
        map_comp := fun f g => Subtype.ext (Prod.ext (Prod.ext (Ve.map_comp f g) (We.map_comp f g)) (congrArg (fun q => q.1.2) (F.map_comp f g))) }
    have hG : ((liftCat V W).app (op (SimplexCategory.mk n))).app (op X) e =
        ((ofCatMap (pr1 a b)).app (op (SimplexCategory.mk n))).app (op X) (show Sx (ofCat (cat1 a b)) n X from G) := by
      first
      | rfl
      | exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => by simp [G, toProd])
    obtain ⟨y, hy1, hy2⟩ := pb_exists (liftCat V W) (ofCatMap (pr1 a b)) e (show Sx (ofCat (cat1 a b)) n X from G) hG
    refine ⟨y, pb_ext ?_ ?_⟩
    · exact (ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app (pullback.lift_fst _ _ hf) _) _) y).trans hy1
    · have k := ConcreteCategory.congr_hom
        (NatTrans.congr_app (NatTrans.congr_app (pullback.lift_snd _ _ hf) (op (SimplexCategory.mk n))) (op X)) y
      refine k.trans ?_
      change ((sigP a b).app _).app _ (((pullback.snd (liftCat V W) (ofCatMap (pr1 a b))).app _).app _ y) = _
      rw [hy2]
      show (G ⋙ toUm a b _ : Fin (n + 1) ⥤ Um (a + b) _) = F
      refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
      apply Subtype.ext
      first
      | (rw [Um_eqToHom_comp, Um_comp_eqToHom]; exact Prod.ext (hb f) rfl)
      | (simp only [Um_eqToHom_comp, Um_comp_eqToHom]; exact Prod.ext (hb f) rfl)
      | (erw [Um_eqToHom_comp, Um_comp_eqToHom]; exact Prod.ext (hb f) rfl)

end LateralTheory.E.LeafHalf1Pf
