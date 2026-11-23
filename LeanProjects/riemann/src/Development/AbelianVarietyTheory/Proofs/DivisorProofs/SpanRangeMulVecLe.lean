import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BlockGLMap

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

theorem span_range_mulVec_le {A : Type} [CommRing A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (v : Fin N → A) :
    Ideal.span (Set.range (M.mulVec v)) ≤ Ideal.span (Set.range v) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem span_range_mulVec_GL {A : Type} [CommRing A] {N : ℕ} (g : GL (Fin N) A) (v : Fin N → A) :
    Ideal.span (Set.range ((g : Matrix (Fin N) (Fin N) A).mulVec v)) = Ideal.span (Set.range v) := by
  refine le_antisymm (span_range_mulVec_le _ _) ?_
  have h := span_range_mulVec_le ((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) ((g : Matrix (Fin N) (Fin N) A).mulVec v)
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h

def Um.smulGL {N : ℕ} {A : Type} [CommRing A] (g : GL (Fin N) A) (v : Um N A) : Um N A :=
  ⟨(g : Matrix (Fin N) (Fin N) A).mulVec v.1, (span_range_mulVec_GL g v.1).trans v.2⟩

theorem Um.smulGL_val {N : ℕ} {A : Type} [CommRing A] (g : GL (Fin N) A) (v : Um N A) :
    (Um.smulGL g v).1 = (g : Matrix (Fin N) (Fin N) A).mulVec v.1 := rfl

theorem Um.smulGL_one {N : ℕ} {A : Type} [CommRing A] (v : Um N A) : Um.smulGL 1 v = v :=
  Subtype.ext (by rw [Um.smulGL_val, Units.val_one, Matrix.one_mulVec])

theorem Um.smulGL_mul {N : ℕ} {A : Type} [CommRing A] (g h : GL (Fin N) A) (v : Um N A) :
    Um.smulGL (g * h) v = Um.smulGL g (Um.smulGL h v) :=
  Subtype.ext (by rw [Um.smulGL_val, Um.smulGL_val, Um.smulGL_val, Units.val_mul, Matrix.mulVec_mulVec])

theorem Um.smulGL_inv_smulGL {N : ℕ} {A : Type} [CommRing A] (g : GL (Fin N) A) (v : Um N A) :
    Um.smulGL g⁻¹ (Um.smulGL g v) = v := by
  rw [← Um.smulGL_mul, inv_mul_cancel, Um.smulGL_one]

theorem Um.smulGL_smulGL_inv {N : ℕ} {A : Type} [CommRing A] (g : GL (Fin N) A) (v : Um N A) :
    Um.smulGL g (Um.smulGL g⁻¹ v) = v := by
  rw [← Um.smulGL_mul, mul_inv_cancel, Um.smulGL_one]

theorem Um.smul_cancel {N : ℕ} {A : Type} [CommRing A] (w : Um N A) {a b : A} (h : a • w.1 = b • w.1) : a = b := by
  have h1 : (1 : A) ∈ Ideal.span (Set.range w.1) := by rw [w.2]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 h1
  have key : ∀ x : A, x = ∑ i, c i * (x * w.1 i) := fun x => by
    calc x = x * ∑ i, c i • w.1 i := by rw [hc, mul_one]
      _ = ∑ i, c i * (x * w.1 i) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [smul_eq_mul]; ring
  rw [key a, key b]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (c i * ·) (congrFun h i)

theorem Um.hom_ext_fst {N : ℕ} {A : Type} [CommRing A] {v w : Um N A} {f f' : v ⟶ w} (h : f.1.1 = f'.1.1) : f = f' := by
  have h2 := f.2
  rw [h] at h2
  exact Subtype.ext (Prod.ext h (Units.ext (Um.smul_cancel w (h2.symm.trans f'.2))))

theorem Um.comp_fst {N : ℕ} {A : Type} [CommRing A] {u v w : Um N A} (f : u ⟶ v) (g : v ⟶ w) :
    (f ≫ g).1.1 = g.1.1 * f.1.1 := rfl

theorem Um.eqToHom_fst {N : ℕ} {A : Type} [CommRing A] {v w : Um N A} (h : v = w) : (eqToHom h).1.1 = 1 := by
  subst h; rfl

theorem Um.functor_ext {N : ℕ} {A : Type} [CommRing A] {C : Type} [Category C] {F F' : C ⥤ Um N A}
    (hobj : ∀ i, F.obj i = F'.obj i) (hmap : ∀ {i j} (f : i ⟶ j), (F.map f).1.1 = (F'.map f).1.1) : F = F' :=
  CategoryTheory.Functor.ext hobj fun i j f => Um.hom_ext_fst (by rw [Um.comp_fst, Um.comp_fst, Um.eqToHom_fst, Um.eqToHom_fst, hmap]; simp)

def FibU (N : ℕ) (A : Type) [CommRing A] : Type := Um N A

instance (N : ℕ) (A : Type) [CommRing A] : SmallCategory (FibU N A) where
  Hom v w := {u : Aˣ // (v : Um N A).1 = (u : A) • (w : Um N A).1}
  id v := ⟨1, by simp⟩
  comp f g := ⟨g.1 * f.1, by rw [Units.val_mul, mul_comm, ← smul_smul, ← g.2, ← f.2]⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

instance (N : ℕ) (A : Type) [CommRing A] (v w : FibU N A) : Subsingleton (v ⟶ w) :=
  ⟨fun f g => Subtype.ext (Units.ext (Um.smul_cancel (w : Um N A) (f.2.symm.trans g.2)))⟩

theorem FibU.functor_ext {N : ℕ} {A : Type} [CommRing A] {C : Type} [Category C] {F F' : C ⥤ FibU N A}
    (hobj : ∀ i, F.obj i = F'.obj i) : F = F' :=
  CategoryTheory.Functor.ext hobj fun _ _ _ => Subsingleton.elim _ _

def FibU.map (N : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : FibU N A ⥤ FibU N B where
  obj v := show FibU N B from (Um.map N f).obj v
  map {v w} u := ⟨Units.map (f : A →* B) u.1, by
    funext i
    have h := congrArg f (congrFun u.2 i)
    simpa [Um.map] using h⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def fibCat (N : ℕ) : CommRingCat.{0} ⥤ Cat.{0,0} where
  obj A := Cat.of (FibU N A)
  map f := (FibU.map N f.hom).toCatHom
  map_id A := rfl
  map_comp f g := rfl

def Fib (N : ℕ) : Spc := ofCat (fibCat N)

def FibU.act {N : ℕ} {A : Type} [CommRing A] (g : GL (Fin N) A) : FibU N A ⥤ FibU N A where
  obj v := show FibU N A from Um.smulGL g v
  map {v w} u := ⟨u.1, by
    change (g : Matrix (Fin N) (Fin N) A).mulVec (v : Um N A).1 = (u.1 : A) • (g : Matrix (Fin N) (Fin N) A).mulVec (w : Um N A).1
    rw [← Matrix.mulVec_smul]; exact congrArg _ u.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def FibU.toLine (N : ℕ) (A : Type) [CommRing A] : FibU N A ⥤ SingleObj (GL (Fin 1) A) where
  obj _ := SingleObj.star _
  map u := Matrix.GeneralLinearGroup.scalar (Fin 1) u.1
  map_id _ := map_one (Matrix.GeneralLinearGroup.scalar (Fin 1))
  map_comp _ _ := map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _

def Fib.line (N : ℕ) : Fib N ⟶ ofCat (glCat 1) :=
  ofCatMap
    { app := fun A => (FibU.toLine N A).toCatHom
      naturality := fun A B f => by
        apply Cat.Hom.ext
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
        change Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map (f.hom : A →* B) p.1) =
          Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) p.1)
        ext i j
        obtain rfl : i = j := Subsingleton.elim _ _
        simp }

def edgeMat {N n : ℕ} {A : Type} [CommRing A] (G : ComposableArrows (SingleObj (GL (Fin N) A)) n) (i : Fin (n + 1)) :
    GL (Fin N) A :=
  G.map (homOfLE (Fin.zero_le i))

theorem edgeMat_map_mul {N n : ℕ} {A : Type} [CommRing A] (G : ComposableArrows (SingleObj (GL (Fin N) A)) n)
    {i j : Fin (n + 1)} (f : i ⟶ j) : (show GL (Fin N) A from G.map f) * edgeMat G i = edgeMat G j := by
  unfold edgeMat
  rw [← SingleObj.comp_as_mul, ← G.map_comp]
  exact congrArg G.map (Subsingleton.elim _ _)

theorem edgeMat_zero {N n : ℕ} {A : Type} [CommRing A] (G : ComposableArrows (SingleObj (GL (Fin N) A)) n) :
    edgeMat G 0 = 1 := by
  unfold edgeMat
  rw [show homOfLE (Fin.zero_le (0 : Fin (n + 1))) = 𝟙 _ from Subsingleton.elim _ _, G.map_id]
  rfl

def vS {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {p : SimplexCategoryᵒᵖ} (U : Scheme.{0}ᵒᵖ) (x : (E.obj p).obj U) :
    ComposableArrows (SingleObj (GL (Fin N) (Scheme.Γ.obj U))) p.unop.len :=
  (V.app p).app U x

theorem vS_map {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {p p' : SimplexCategoryᵒᵖ} (θ : p ⟶ p') (U : Scheme.{0}ᵒᵖ)
    (x : (E.obj p).obj U) :
    vS V U ((E.map θ).app U x) = (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ vS V U x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (V.naturality θ) U) x

theorem vS_natU {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {p : SimplexCategoryᵒᵖ} {U U' : Scheme.{0}ᵒᵖ} (f : U ⟶ U')
    (x : (E.obj p).obj U) :
    vS V U' ((E.obj p).map f x) = vS V U x ⋙ SingleObj.mapHom _ _ (Matrix.GeneralLinearGroup.map (Scheme.Γ.map f).hom) :=
  ConcreteCategory.congr_hom ((V.app p).naturality f) x

def hMat {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {p p' : SimplexCategoryᵒᵖ} (θ : p ⟶ p') (U : Scheme.{0}ᵒᵖ)
    (x : (E.obj p).obj U) : GL (Fin N) (Scheme.Γ.obj U) :=
  edgeMat (vS V U x) (θ.unop.toOrderHom 0)

theorem hMat_id {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (p : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ)
    (x : (E.obj p).obj U) : hMat V (𝟙 p) U x = 1 :=
  edgeMat_zero _

theorem hMat_comp {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {p p' p'' : SimplexCategoryᵒᵖ} (θ : p ⟶ p') (φ : p' ⟶ p'')
    (U : Scheme.{0}ᵒᵖ) (x : (E.obj p).obj U) :
    hMat V (θ ≫ φ) U x = hMat V φ U ((E.map θ).app U x) * hMat V θ U x := by
  unfold hMat
  rw [vS_map]
  exact (edgeMat_map_mul (vS V U x) (homOfLE (θ.unop.toOrderHom.monotone (Fin.zero_le (φ.unop.toOrderHom 0))))).symm

theorem hMat_natU {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {p p' : SimplexCategoryᵒᵖ} (θ : p ⟶ p') {U U' : Scheme.{0}ᵒᵖ}
    (f : U ⟶ U') (x : (E.obj p).obj U) :
    hMat V θ U' ((E.obj p).map f x) = Matrix.GeneralLinearGroup.map (Scheme.Γ.map f).hom (hMat V θ U x) := by
  unfold hMat
  rw [vS_natU]
  rfl

theorem Um.map_smulGL {N : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin N) A) (v : Um N A) :
    (Um.map N f).obj (Um.smulGL g v) = Um.smulGL (Matrix.GeneralLinearGroup.map f g) ((Um.map N f).obj v) := by
  apply Subtype.ext
  funext i
  change f (((g : Matrix (Fin N) (Fin N) A).mulVec v.1) i) = _
  rw [RingHom.map_mulVec]
  rfl

def ptimes (P : PSh) (S : Spc) : Spc where
  obj n :=
    { obj := fun U => P.obj U × (S.obj n).obj U
      map := fun f => TypeCat.ofHom fun y => (P.map f y.1, (S.obj n).map f y.2)
      map_id := fun U => by ext y <;> simp
      map_comp := fun f g => by ext y <;> simp }
  map θ :=
    { app := fun U => TypeCat.ofHom fun y => (y.1, (S.map θ).app U y.2)
      naturality := fun U U' f => by
        ext y
        · rfl
        · exact ConcreteCategory.congr_hom ((S.map θ).naturality f) y.2 }
  map_id n := by ext U y <;> simp
  map_comp θ φ := by ext U y <;> simp

abbrev actC {N n : ℕ} {A : Type} [CommRing A] (g : GL (Fin N) A) (w : ComposableArrows (FibU N A) n) :
    ComposableArrows (FibU N A) n :=
  w ⋙ FibU.act g

theorem actC_one {N n : ℕ} {A : Type} [CommRing A] (w : ComposableArrows (FibU N A) n) : actC 1 w = w :=
  FibU.functor_ext fun i => Um.smulGL_one (w.obj i)

theorem actC_mul {N n : ℕ} {A : Type} [CommRing A] (g h : GL (Fin N) A) (w : ComposableArrows (FibU N A) n) :
    actC (g * h) w = actC g (actC h w) :=
  FibU.functor_ext fun i => Um.smulGL_mul g h (w.obj i)

def twMap (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) {p p' : SimplexCategoryᵒᵖ} (θ : p ⟶ p') (k : SimplexCategoryᵒᵖ)
    (U : Scheme.{0}ᵒᵖ) (y : (E.obj p).obj U × ((Fib N).obj k).obj U) : (E.obj p').obj U × ((Fib N).obj k).obj U :=
  ((E.map θ).app U y.1,
    actC (hMat V θ U y.1) (show ComposableArrows (FibU N (Scheme.Γ.obj U)) k.unop.len from y.2))

def twX (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) : SimplicialObject Spc where
  obj p := ptimes (E.obj p) (Fib N)
  map θ :=
    { app := fun k =>
        { app := fun U => TypeCat.ofHom (twMap E V θ k U)
          naturality := fun U U' f => by
            ext y
            refine Prod.ext ?_ ?_
            · exact ConcreteCategory.congr_hom ((E.map θ).naturality f) y.1
            · change actC (hMat V θ U' ((E.obj _).map f y.1)) _ = _
              rw [hMat_natU]
              exact FibU.functor_ext fun i => (Um.map_smulGL _ _ _).symm }
      naturality := fun k k' ψ => rfl }
  map_id p := by
    ext k U y
    refine Prod.ext ?_ ?_
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app (E.map_id p) U) y.1
    · change actC (hMat V (𝟙 p) U y.1) _ = _
      rw [hMat_id, actC_one]
      rfl
  map_comp θ φ := by
    ext k U y
    refine Prod.ext ?_ ?_
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app (E.map_comp θ φ) U) y.1
    · change actC (hMat V (θ ≫ φ) U y.1) _ = _
      rw [hMat_comp, actC_mul]
      rfl

def bidiag : SimplicialObject Spc ⥤ Spc :=
  Functor.uncurry ⋙ (Functor.whiskeringLeft _ _ PSh).obj (Functor.diag SimplexCategoryᵒᵖ)

def bidiagConst (S : Spc) : bidiag.obj ((Functor.const SimplexCategoryᵒᵖ).obj S) ≅ S :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [bidiag])

def twistC {N n : ℕ} {A : Type} [CommRing A] (G : ComposableArrows (SingleObj (GL (Fin N) A)) n)
    (w : ComposableArrows (FibU N A) n) : ComposableArrows (Um N A) n where
  obj i := Um.smulGL (edgeMat G i) (w.obj i)
  map {i j} f := ⟨(G.map f, (w.map f).1), by
    change ((show GL (Fin N) A from G.map f) : Matrix (Fin N) (Fin N) A).mulVec
        ((edgeMat G i : Matrix (Fin N) (Fin N) A).mulVec (w.obj i : Um N A).1) =
      ((w.map f).1 : A) • (edgeMat G j : Matrix (Fin N) (Fin N) A).mulVec (w.obj j : Um N A).1
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, edgeMat_map_mul, ← Matrix.mulVec_smul]
    exact congrArg _ (w.map f).2⟩
  map_id i := Subtype.ext (Prod.ext (G.map_id i) (congrArg Subtype.val (w.map_id i)))
  map_comp f g := Subtype.ext (Prod.ext (G.map_comp f g) (congrArg Subtype.val (w.map_comp f g)))

theorem twistC_toGL {N n : ℕ} {A : Type} [CommRing A] (G : ComposableArrows (SingleObj (GL (Fin N) A)) n)
    (w : ComposableArrows (FibU N A) n) : twistC G w ⋙ Um.toGL N A = G :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl)

def twPi (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) : bidiag.obj (twX E V) ⟶ E where
  app n :=
    { app := fun U => TypeCat.ofHom fun y => (show (E.obj n).obj U × ((Fib N).obj n).obj U from y).1
      naturality := fun _ _ _ => rfl }
  naturality _ _ _ := rfl

def twSigma (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) : bidiag.obj (twX E V) ⟶ PGL N where
  app n :=
    { app := fun U => TypeCat.ofHom fun y =>
        twistC (vS V U (show (E.obj n).obj U × ((Fib N).obj n).obj U from y).1)
          (show ComposableArrows (FibU N (Scheme.Γ.obj U)) n.unop.len from
            (show (E.obj n).obj U × ((Fib N).obj n).obj U from y).2)
      naturality := fun U U' f => by
        ext y
        change twistC (vS V U' ((E.obj n).map f y.1)) _ = _
        rw [vS_natU]
        exact Um.functor_ext (fun i => (Um.map_smulGL _ _ _).symm) (fun _ => rfl) }
  naturality n n' θ := by
    ext U y
    change twistC (vS V U ((E.map θ).app U y.1)) _ = _
    rw [vS_map]
    refine Um.functor_ext (fun i => ?_) (fun _ => rfl)
    change Um.smulGL _ (Um.smulGL (hMat V θ U y.1) _) = Um.smulGL _ _
    refine (Um.smulGL_mul _ _ _).symm.trans ?_
    congr 1
    exact edgeMat_map_mul (vS V U y.1) (homOfLE (θ.unop.toOrderHom.monotone (Fin.zero_le i)))

theorem twPi_twSigma (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) : twPi E V ≫ V = twSigma E V ≫ PGL.pr N := by
  ext n U y
  exact (twistC_toGL _ _).symm

def ptimes.snd (P : PSh) (S : Spc) : ptimes P S ⟶ S where
  app n := { app := fun U => TypeCat.ofHom fun y => y.2, naturality := fun _ _ _ => rfl }
  naturality _ _ _ := rfl

def ptimes.fst (P : PSh) (S : Spc) : ptimes P S ⟶ disc.obj P where
  app n := { app := fun U => TypeCat.ofHom fun y => y.1, naturality := fun _ _ _ => rfl }
  naturality _ _ _ := rfl

def twLine (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) :
    twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (ofCat (glCat 1)) where
  app p := ptimes.snd (E.obj p) (Fib N) ≫ Fib.line N
  naturality _ _ _ := rfl

theorem twSigma_line (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) :
    twSigma E V ≫ PGL.line N = bidiag.map (twLine E V) ≫ (bidiagConst _).hom :=
  rfl

theorem twistC_injective {N n : ℕ} {A : Type} [CommRing A] (G : ComposableArrows (SingleObj (GL (Fin N) A)) n)
    {w w' : ComposableArrows (FibU N A) n} (h : twistC G w = twistC G w') : w = w' :=
  FibU.functor_ext fun i => by
    have h' := congrArg (fun F : ComposableArrows (Um N A) n => Um.smulGL (edgeMat G i)⁻¹ (F.obj i)) h
    change Um.smulGL _ (Um.smulGL _ (w.obj i)) = Um.smulGL _ (Um.smulGL _ (w'.obj i)) at h'
    exact (Um.smulGL_inv_smulGL (edgeMat G i) (w.obj i : Um N A)).symm.trans (h'.trans (Um.smulGL_inv_smulGL _ _))

def untwistC {N n : ℕ} {A : Type} [CommRing A] (G : ComposableArrows (SingleObj (GL (Fin N) A)) n)
    (F : ComposableArrows (Um N A) n) (hF : F ⋙ Um.toGL N A = G) : ComposableArrows (FibU N A) n where
  obj i := show FibU N A from Um.smulGL (edgeMat G i)⁻¹ (F.obj i)
  map {i j} f := ⟨(F.map f).1.2, by
    have hg : (F.map f).1.1 = (show GL (Fin N) A from G.map f) := by
      have := CategoryTheory.Functor.congr_hom hF f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at this
      exact this
    have e : (edgeMat G i)⁻¹ = (edgeMat G j)⁻¹ * (show GL (Fin N) A from G.map f) := by
      rw [← edgeMat_map_mul G f, mul_inv_rev, inv_mul_cancel_right]
    change (((edgeMat G i)⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A).mulVec (F.obj i).1 =
      ((F.map f).1.2 : A) • (((edgeMat G j)⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A).mulVec (F.obj j).1
    rw [e, Units.val_mul, ← Matrix.mulVec_mulVec, ← hg, (F.map f).2, Matrix.mulVec_smul]⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem twistC_untwistC {N n : ℕ} {A : Type} [CommRing A] (G : ComposableArrows (SingleObj (GL (Fin N) A)) n)
    (F : ComposableArrows (Um N A) n) (hF : F ⋙ Um.toGL N A = G) : twistC G (untwistC G F hF) = F :=
  Um.functor_ext (fun i => Um.smulGL_smulGL_inv _ _) (fun f => by
    have := CategoryTheory.Functor.congr_hom hF f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at this
    exact this.symm)

def twIsLimit (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) :
    IsLimit (PullbackCone.mk (twPi E V) (twSigma E V) (twPi_twSigma E V)) := by
  apply evaluationJointlyReflectsLimits
  intro n
  refine (isLimitMapConePullbackConeEquiv _ _).2 ?_
  apply evaluationJointlyReflectsLimits
  intro U
  refine (isLimitMapConePullbackConeEquiv _ _).2 ?_
  refine (PullbackCone.isLimitEquivBijective _).symm ⟨?_, ?_⟩
  · intro y y' h
    have h1 := congrArg (fun z => z.1.1) h
    have h2 := congrArg (fun z => z.1.2) h
    change (show (E.obj n).obj U × ((Fib N).obj n).obj U from y).1 =
      (show (E.obj n).obj U × ((Fib N).obj n).obj U from y').1 at h1
    change twistC (vS V U (show (E.obj n).obj U × ((Fib N).obj n).obj U from y).1) _ =
      twistC (vS V U (show (E.obj n).obj U × ((Fib N).obj n).obj U from y').1) _ at h2
    rw [← h1] at h2
    exact Prod.ext h1 (twistC_injective _ h2)
  · rintro ⟨⟨x, F⟩, hF⟩
    refine ⟨(show (E.obj n).obj U × ((Fib N).obj n).obj U from (x, untwistC (vS V U x) F hF.symm)), ?_⟩
    exact Subtype.ext (Prod.ext rfl (twistC_untwistC (vS V U x) F hF.symm))

def twIso (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) : bidiag.obj (twX E V) ≅ pullback V (PGL.pr N) :=
  (twIsLimit E V).conePointUniqueUpToIso (t := PullbackCone.mk _ _ pullback.condition) (pullbackIsPullback V (PGL.pr N))

theorem twIso_hom_fst (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) :
    (twIso E V).hom ≫ pullback.fst V (PGL.pr N) = twPi E V :=
  (twIsLimit E V).conePointUniqueUpToIso_hom_comp (pullbackIsPullback V (PGL.pr N)) WalkingCospan.left

theorem twIso_hom_snd (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) :
    (twIso E V).hom ≫ pullback.snd V (PGL.pr N) = twSigma E V :=
  (twIsLimit E V).conePointUniqueUpToIso_hom_comp (pullbackIsPullback V (PGL.pr N)) WalkingCospan.right

theorem twIso_line (E : Spc) {N : ℕ} (V : E ⟶ ofCat (glCat N)) :
    (twIso E V).hom ≫ pullback.snd V (PGL.pr N) ≫ PGL.line N = bidiag.map (twLine E V) ≫ (bidiagConst _).hom := by
  rw [← Category.assoc, twIso_hom_snd]
  exact twSigma_line E V

def ptimesIsLimit (P : PSh) (S : Spc) : IsLimit (BinaryFan.mk (ptimes.fst P S) (ptimes.snd P S)) :=
  BinaryFan.IsLimit.mk _
    (fun {T} a b =>
      { app := fun n =>
          { app := fun U => TypeCat.ofHom fun z => ((a.app n).app U z, (b.app n).app U z)
            naturality := fun U U' f => by
              ext z
              refine Prod.ext ?_ ?_
              · exact ConcreteCategory.congr_hom ((a.app n).naturality f) z
              · exact ConcreteCategory.congr_hom ((b.app n).naturality f) z }
        naturality := fun n n' θ => by
          ext U z
          refine Prod.ext ?_ ?_
          · exact ConcreteCategory.congr_hom (NatTrans.congr_app (a.naturality θ) U) z
          · exact ConcreteCategory.congr_hom (NatTrans.congr_app (b.naturality θ) U) z })
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun a b m h1 h2 => by
      ext n U z
      refine Prod.ext ?_ ?_
      · exact ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app h1 n) U) z
      · exact ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app h2 n) U) z)

def ptimesIso (P : PSh) (S : Spc) : ptimes P S ≅ disc.obj P ⨯ S :=
  (ptimesIsLimit P S).conePointUniqueUpToIso (t := BinaryFan.mk prod.fst prod.snd) (prodIsProd (disc.obj P) S)

theorem disc_vS_map {P : PSh} {N : ℕ} (V₀ : disc.obj P ⟶ ofCat (glCat N)) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ)
    (x : P.obj U) {i j : Fin (n.unop.len + 1)} (f : i ⟶ j) :
    (show GL (Fin N) (Scheme.Γ.obj U) from (vS V₀ (p := n) U x).map f) = 1 := by
  have h := vS_map V₀ (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op U (p := op (SimplexCategory.mk 0)) x
  change vS V₀ (p := n) U x = _ at h
  rw [h]
  have e : @Eq ((0 : Fin (0 + 1)) ⟶ 0)
      ((SimplexCategory.toCat.map (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0).op.unop).toFunctor.map f)
      (𝟙 (0 : Fin (0 + 1))) := Subsingleton.elim _ _
  exact (congrArg (vS V₀ (p := op (SimplexCategory.mk 0)) U x).map e).trans
    ((vS V₀ (p := op (SimplexCategory.mk 0)) U x).map_id _)

theorem disc_hMat {P : PSh} {N : ℕ} (V₀ : disc.obj P ⟶ ofCat (glCat N)) {p p' : SimplexCategoryᵒᵖ} (θ : p ⟶ p')
    (U : Scheme.{0}ᵒᵖ) (x : P.obj U) : hMat V₀ θ U x = 1 :=
  disc_vS_map V₀ p U x _

def discDiagIso (P : PSh) {N : ℕ} (V₀ : disc.obj P ⟶ ofCat (glCat N)) :
    bidiag.obj (twX (disc.obj P) V₀) ≅ ptimes P (Fib N) where
  hom :=
    { app := fun n => { app := fun U => TypeCat.ofHom fun y => y, naturality := fun _ _ _ => rfl }
      naturality := fun n n' θ => by
        ext U y
        change ((show P.obj U × ((Fib N).obj n).obj U from y).1,
          (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ actC (hMat V₀ θ U (show P.obj U × ((Fib N).obj n).obj U from y).1)
            (show P.obj U × ((Fib N).obj n).obj U from y).2) = _
        rw [disc_hMat]
        exact congrArg (fun w : ComposableArrows (FibU N (Scheme.Γ.obj U)) n.unop.len =>
          ((show P.obj U × ((Fib N).obj n).obj U from y).1,
            (show ((Fib N).obj n').obj U from (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ w)))
          (actC_one (show ComposableArrows (FibU N (Scheme.Γ.obj U)) n.unop.len from
            (show P.obj U × ((Fib N).obj n).obj U from y).2)) }
  inv :=
    { app := fun n => { app := fun U => TypeCat.ofHom fun y => y, naturality := fun _ _ _ => rfl }
      naturality := fun n n' θ => by
        ext U y
        change _ = ((show P.obj U × ((Fib N).obj n).obj U from y).1,
          (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ actC (hMat V₀ θ U (show P.obj U × ((Fib N).obj n).obj U from y).1)
            (show P.obj U × ((Fib N).obj n).obj U from y).2)
        rw [disc_hMat]
        exact congrArg (fun w : ComposableArrows (FibU N (Scheme.Γ.obj U)) n.unop.len =>
          ((show P.obj U × ((Fib N).obj n).obj U from y).1,
            (show ((Fib N).obj n').obj U from (SimplexCategory.toCat.map θ.unop).toFunctor ⋙ w)))
          (actC_one (show ComposableArrows (FibU N (Scheme.Γ.obj U)) n.unop.len from
            (show P.obj U × ((Fib N).obj n).obj U from y).2)).symm }
  hom_inv_id := rfl
  inv_hom_id := rfl

def colIso (P : PSh) {N : ℕ} (V₀ : disc.obj P ⟶ ofCat (glCat N)) : ptimes P (Fib N) ≅ pullback V₀ (PGL.pr N) :=
  (discDiagIso P V₀).symm ≪≫ twIso (disc.obj P) V₀

theorem colIso_hom_fst (P : PSh) {N : ℕ} (V₀ : disc.obj P ⟶ ofCat (glCat N)) :
    (colIso P V₀).hom ≫ pullback.fst V₀ (PGL.pr N) = ptimes.fst P (Fib N) := by
  rw [colIso, Iso.trans_hom, Category.assoc, twIso_hom_fst]
  rfl

theorem colIso_line (P : PSh) {N : ℕ} (V₀ : disc.obj P ⟶ ofCat (glCat N)) :
    (colIso P V₀).hom ≫ pullback.snd V₀ (PGL.pr N) ≫ PGL.line N = ptimes.snd P (Fib N) ≫ Fib.line N := by
  rw [colIso, Iso.trans_hom, Category.assoc, twIso_line]
  rfl

end GlobalTheory.EtC

end
