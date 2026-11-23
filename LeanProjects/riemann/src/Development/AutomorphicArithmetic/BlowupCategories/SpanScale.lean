import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.Blow

def mulS (E Z : Spc) : Spc where
  obj k :=
    { obj := fun T => (E.obj k).obj T × (Z.obj k).obj T
      map := fun f => TypeCat.ofHom fun x => ((E.obj k).map f x.1, (Z.obj k).map f x.2)
      map_id := fun T => by ext x <;> simp
      map_comp := fun f g => by ext x <;> simp }
  map f :=
    { app := fun T => TypeCat.ofHom fun x => ((E.map f).app T x.1, (Z.map f).app T x.2)
      naturality := fun T T' g => by
        ext x
        · exact ConcreteCategory.congr_hom ((E.map f).naturality g) x.1
        · exact ConcreteCategory.congr_hom ((Z.map f).naturality g) x.2 }
  map_id k := by ext T x <;> simp
  map_comp f g := by ext T x <;> simp

def mulS.fst (E Z : Spc) : mulS E Z ⟶ E where
  app k := { app := fun T => TypeCat.ofHom fun x => x.1, naturality := fun _ _ _ => rfl }
  naturality _ _ _ := rfl

def mulS.snd (E Z : Spc) : mulS E Z ⟶ Z where
  app k := { app := fun T => TypeCat.ofHom fun x => x.2, naturality := fun _ _ _ => rfl }
  naturality _ _ _ := rfl

def mulS.lift {S E Z : Spc} (f : S ⟶ E) (g : S ⟶ Z) : S ⟶ mulS E Z where
  app k :=
    { app := fun T => TypeCat.ofHom fun x => ((f.app k).app T x, (g.app k).app T x)
      naturality := fun T T' h => by
        ext x
        have h1 := ConcreteCategory.congr_hom ((f.app k).naturality h) x
        have h2 := ConcreteCategory.congr_hom ((g.app k).naturality h) x
        exact Prod.ext h1 h2 }
  naturality m n h := by
    ext T x
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (f.naturality h) T) x
    have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (g.naturality h) T) x
    exact Prod.ext h1 h2

structure Act where
  D : CommRingCat.{0} ⥤ Type
  G : CommRingCat.{0} ⥤ GrpCat.{0}
  smul : ∀ A : CommRingCat.{0}, G.obj A → D.obj A → D.obj A
  one_smul : ∀ (A : CommRingCat.{0}) (x : D.obj A), smul A 1 x = x
  mul_smul : ∀ (A : CommRingCat.{0}) (g h : G.obj A) (x : D.obj A), smul A (g * h) x = smul A g (smul A h x)
  nat : ∀ {A B : CommRingCat.{0}} (f : A ⟶ B) (g : G.obj A) (x : D.obj A),
    D.map f (smul A g x) = smul B (G.map f g) (D.map f x)

structure Ob (a : Act) (A : CommRingCat.{0}) where
  pt : a.D.obj A

instance (a : Act) (A : CommRingCat.{0}) : SmallCategory (Ob a A) where
  Hom x y := {g : a.G.obj A // x.pt = a.smul A g y.pt}
  id x := ⟨1, (a.one_smul A _).symm⟩
  comp f g := ⟨f.1 * g.1, by rw [a.mul_smul, ← g.2, ← f.2]⟩
  id_comp f := Subtype.ext (one_mul _)
  comp_id f := Subtype.ext (mul_one _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _)

theorem Ob.hom_heq {a : Act} {A : CommRingCat.{0}} {x x' y y' : Ob a A} (hx : x = x') (hy : y = y') (f : x ⟶ y) (f' : x' ⟶ y')
    (h : f.1 = f'.1) : HEq f f' := by
  subst hx hy
  exact heq_of_eq (Subtype.ext h)

def Ob.map (a : Act) {A B : CommRingCat.{0}} (f : A ⟶ B) : Ob a A ⥤ Ob a B where
  obj x := ⟨a.D.map f x.pt⟩
  map {x y} g := ⟨a.G.map f g.1, (congrArg (a.D.map f) g.2).trans (a.nat f g.1 y.pt)⟩
  map_id x := Subtype.ext (map_one (a.G.map f).hom)
  map_comp g h := Subtype.ext (map_mul (a.G.map f).hom _ _)

def Act.cat (a : Act) : CommRingCat.{0} ⥤ Cat.{0,0} where
  obj A := Cat.of (Ob a A)
  map f := (Ob.map a f).toCatHom
  map_id A := by
    apply Cat.Hom.ext
    have ho : ∀ x : Ob a A, (Ob.map a (𝟙 A)).obj x = x := fun x => by
      cases x
      simp [Ob.map]
    refine CategoryTheory.Functor.hext ho (fun x y g => Ob.hom_heq (ho x) (ho y) _ _ ?_)
    simp [Ob.map]
    rfl
  map_comp {A B C} f g := by
    apply Cat.Hom.ext
    have ho : ∀ x : Ob a A, (Ob.map a (f ≫ g)).obj x = (Ob.map a g).obj ((Ob.map a f).obj x) := fun x => by
      cases x
      simp [Ob.map]
    refine CategoryTheory.Functor.hext ho (fun x y h => Ob.hom_heq (ho x) (ho y) _ _ ?_)
    simp [Ob.map]
    rfl

structure Act.Hom (a b : Act) where
  d : a.D ⟶ b.D
  g : a.G ⟶ b.G
  eq : ∀ (A : CommRingCat.{0}) (u : a.G.obj A) (x : a.D.obj A), d.app A (a.smul A u x) = b.smul A (g.app A u) (d.app A x)

def Act.Hom.comp {a b c : Act} (φ : Act.Hom a b) (ψ : Act.Hom b c) : Act.Hom a c where
  d := φ.d ≫ ψ.d
  g := φ.g ≫ ψ.g
  eq A u x := by
    simp only [NatTrans.comp_app, types_comp_apply, ConcreteCategory.comp_apply]
    rw [φ.eq, ψ.eq]

def Act.Hom.fn {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0}) : Ob a A ⥤ Ob b A where
  obj x := ⟨φ.d.app A x.pt⟩
  map {x y} f := ⟨φ.g.app A f.1, (congrArg (φ.d.app A) f.2).trans (φ.eq A f.1 y.pt)⟩
  map_id x := Subtype.ext (map_one (φ.g.app A).hom)
  map_comp f g := Subtype.ext (map_mul (φ.g.app A).hom _ _)

def Act.Hom.cat {a b : Act} (φ : Act.Hom a b) : a.cat ⟶ b.cat where
  app A := (φ.fn A).toCatHom
  naturality {A B} f := by
    apply Cat.Hom.ext
    have ho : ∀ x : Ob a A, (φ.fn B).obj ((Ob.map a f).obj x) = (Ob.map b f).obj ((φ.fn A).obj x) := fun x =>
      congrArg Ob.mk (ConcreteCategory.congr_hom (φ.d.naturality f) x.pt)
    refine CategoryTheory.Functor.hext ho (fun x y h => Ob.hom_heq (ho x) (ho y) _ _ ?_)
    exact ConcreteCategory.congr_hom (φ.g.naturality f) h.1

abbrev spc (a : Act) : Spc := ofCat a.cat

abbrev spcMap {a b : Act} (φ : Act.Hom a b) : spc a ⟶ spc b := ofCatMap φ.cat

abbrev Sp (E : Spc) (a : Act) : Spc := mulS E (spc a)

abbrev Sp.fst (E : Spc) (a : Act) : Sp E a ⟶ E := mulS.fst _ _

abbrev Sp.snd (E : Spc) (a : Act) : Sp E a ⟶ spc a := mulS.snd _ _

abbrev Sp.map (E : Spc) {a b : Act} (φ : Act.Hom a b) : Sp E a ⟶ Sp E b :=
  mulS.lift (Sp.fst E a) (Sp.snd E a ≫ spcMap φ)

abbrev Sp.pair (E : Spc) {a b c : Act} (ρ : Act.Hom a b) (σ : Act.Hom a c) : Sp E a ⟶ Sp (Sp E b) c :=
  mulS.lift (Sp.map E ρ) (Sp.snd E a ≫ spcMap σ)

def gmF : CommRingCat.{0} ⥤ GrpCat.{0} where
  obj A := GrpCat.of Aˣ
  map f := GrpCat.ofHom (Units.map (f.hom : _ →* _))
  map_id A := by ext; rfl
  map_comp f g := by ext; rfl

def lineFn {a : Act} (χ : a.G ⟶ gmF) (A : CommRingCat.{0}) : Ob a A ⥤ SingleObj (GL (Fin 1) A) where
  obj _ := SingleObj.star _
  map f := Matrix.GeneralLinearGroup.scalar (Fin 1) (show Aˣ from χ.app A f.1)
  map_id x := by
    change Matrix.GeneralLinearGroup.scalar (Fin 1) (show Aˣ from χ.app A 1) = 1
    rw [map_one (χ.app A).hom]
    exact map_one _
  map_comp f g := by
    have h : (show Aˣ from χ.app A (f.1 * g.1)) = (show Aˣ from χ.app A g.1) * (show Aˣ from χ.app A f.1) := by
      rw [mul_comm]
      exact map_mul (χ.app A).hom _ _
    change Matrix.GeneralLinearGroup.scalar (Fin 1) (show Aˣ from χ.app A (f.1 * g.1)) = _
    rw [h]
    exact map_mul (Matrix.GeneralLinearGroup.scalar (Fin 1)) _ _

def lineOf {a : Act} (χ : a.G ⟶ gmF) : spc a ⟶ ofCat (glCat 1) :=
  ofCatMap
    { app := fun A => (lineFn χ A).toCatHom
      naturality := fun A B f => by
        apply Cat.Hom.ext
        refine CategoryTheory.Functor.hext (fun _ => rfl) (fun v w p => heq_of_eq ?_)
        have h : (show Bˣ from χ.app B (a.G.map f p.1)) = Units.map (f.hom : _ →* _) (show Aˣ from χ.app A p.1) :=
          ConcreteCategory.congr_hom (χ.naturality f) p.1
        have key : ∀ u : Aˣ, Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map (f.hom : _ →* _) u) =
            Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) u) := fun u => by
          ext i j
          obtain rfl : i = j := Subsingleton.elim _ _
          simp
        change Matrix.GeneralLinearGroup.scalar (Fin 1) (show Bˣ from χ.app B (a.G.map f p.1)) =
          Matrix.GeneralLinearGroup.map f.hom (Matrix.GeneralLinearGroup.scalar (Fin 1) (show Aˣ from χ.app A p.1))
        rw [h]
        exact key _ }

abbrev Sp.line (E : Spc) {a : Act} (χ : a.G ⟶ gmF) : Sp E a ⟶ ofCat (glCat 1) := Sp.snd E a ≫ lineOf χ

structure Pred (a : Act) where
  P : ∀ A : CommRingCat.{0}, a.D.obj A → Prop
  map : ∀ {A B : CommRingCat.{0}} (f : A ⟶ B) (x : a.D.obj A), P A x → P B (a.D.map f x)
  smul : ∀ (A : CommRingCat.{0}) (g : a.G.obj A) (x : a.D.obj A), P A (a.smul A g x) ↔ P A x

def Pred.Le {a : Act} (Q R : Pred a) : Prop := ∀ (A : CommRingCat.{0}) (x : a.D.obj A), Q.P A x → R.P A x

def Pred.inf {a : Act} (Q R : Pred a) : Pred a where
  P A x := Q.P A x ∧ R.P A x
  map f x h := ⟨Q.map f x h.1, R.map f x h.2⟩
  smul A g x := and_congr (Q.smul A g x) (R.smul A g x)

def Pred.top (a : Act) : Pred a where
  P _ _ := True
  map _ _ _ := trivial
  smul _ _ _ := Iff.rfl

def Pred.comap {a b : Act} (φ : Act.Hom a b) (Q : Pred b) : Pred a where
  P A x := Q.P A (φ.d.app A x)
  map {A B} f x h := by
    have e : φ.d.app B (a.D.map f x) = b.D.map f (φ.d.app A x) := ConcreteCategory.congr_hom (φ.d.naturality f) x
    rw [e]
    exact Q.map f _ h
  smul A g x := by
    rw [φ.eq]
    exact Q.smul A _ _

def Act.sub (a : Act) (Q : Pred a) : Act where
  D :=
    { obj := fun A => {x : a.D.obj A // Q.P A x}
      map := fun f => TypeCat.ofHom fun x => ⟨a.D.map f x.1, Q.map f x.1 x.2⟩
      map_id := fun A => by
        ext x
        exact ConcreteCategory.congr_hom (a.D.map_id A) x.1
      map_comp := fun f g => by
        ext x
        exact ConcreteCategory.congr_hom (a.D.map_comp f g) x.1 }
  G := a.G
  smul A g x := ⟨a.smul A g x.1, (Q.smul A g x.1).2 x.2⟩
  one_smul A x := Subtype.ext (a.one_smul A x.1)
  mul_smul A g h x := Subtype.ext (a.mul_smul A g h x.1)
  nat f g x := Subtype.ext (a.nat f g x.1)

def incl {a : Act} (Q : Pred a) : Act.Hom (a.sub Q) a where
  d := { app := fun A => TypeCat.ofHom fun x => x.1, naturality := fun _ _ _ => rfl }
  g := 𝟙 _
  eq _ _ _ := rfl

def inclLe {a : Act} {Q R : Pred a} (h : Q.Le R) : Act.Hom (a.sub Q) (a.sub R) where
  d := { app := fun A => TypeCat.ofHom fun x => ⟨x.1, h A x.1 x.2⟩, naturality := fun _ _ _ => rfl }
  g := 𝟙 _
  eq _ _ _ := rfl

def Act.Hom.sub {a b : Act} (φ : Act.Hom a b) (Q : Pred b) : Act.Hom (a.sub (Q.comap φ)) (b.sub Q) where
  d :=
    { app := fun A => TypeCat.ofHom fun x => ⟨φ.d.app A x.1, x.2⟩
      naturality := fun A B f => by
        ext x
        have h := ConcreteCategory.congr_hom (φ.d.naturality f) x.1
        refine Subtype.ext ?_
        exact h }
  g := φ.g
  eq A u x := Subtype.ext (φ.eq A u x.1)

def Um.scale {M : ℕ} {A : Type} [CommRing A] (c : Fin M → Aˣ) (v : Um M A) : Um M A :=
  ⟨fun i => (c i : A) * v.1 i, by
    refine top_le_iff.1 (le_trans (le_of_eq v.2.symm) (Ideal.span_le.2 ?_))
    rintro _ ⟨i, rfl⟩
    have h : v.1 i = ((c i)⁻¹ : Aˣ) * ((c i : A) * v.1 i) := by simp
    rw [h]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)⟩

theorem Um.scale_one {M : ℕ} {A : Type} [CommRing A] (v : Um M A) : Um.scale (fun _ => 1) v = v :=
  Subtype.ext (by funext i; simp [Um.scale])

theorem Um.scale_mul {M : ℕ} {A : Type} [CommRing A] (c d : Fin M → Aˣ) (v : Um M A) :
    Um.scale (fun i => c i * d i) v = Um.scale c (Um.scale d v) :=
  Subtype.ext (by funext i; simp [Um.scale, mul_assoc])

theorem Um.map_scale {M : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c : Fin M → Aˣ) (v : Um M A) :
    (Um.map M f).obj (Um.scale c v) = Um.scale (fun i => Units.map (f : A →* B) (c i)) ((Um.map M f).obj v) :=
  Subtype.ext (by funext i; simp [Um.scale, Um.map])

def umD (M : ℕ) : CommRingCat.{0} ⥤ Type where
  obj A := Um M A
  map f := TypeCat.ofHom (Um.map M f.hom).obj
  map_id A := by
    ext v
    rfl
  map_comp f g := by
    ext v
    rfl

def XC (M : ℕ) : Act where
  D := umD M
  G := gmF
  smul A u v := Um.scale (fun _ => u) v
  one_smul A v := Um.scale_one (A := A) v
  mul_smul A g h v := Um.scale_mul (A := A) (fun _ => g) (fun _ => h) v
  nat f g x := Um.map_scale f.hom (fun _ => g) x

def bAct {N : ℕ} {A : Type} [CommRing A] (g : Aˣ × Aˣ) (x : Um N A × Um 2 A) : Um N A × Um 2 A :=
  (Um.scale (fun _ => g.1) x.1, Um.scale ![g.2 * g.1⁻¹, g.2] x.2)

theorem bAct_one {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A) : bAct 1 x = x := by
  refine Prod.ext (Um.scale_one x.1) (Subtype.ext (funext fun i => ?_))
  fin_cases i <;> simp [bAct, Um.scale]

theorem bAct_mul {N : ℕ} {A : Type} [CommRing A] (g h : Aˣ × Aˣ) (x : Um N A × Um 2 A) : bAct (g * h) x = bAct g (bAct h x) := by
  have e : (g * h).2 * (g * h).1⁻¹ = (g.2 * g.1⁻¹) * (h.2 * h.1⁻¹) := by
    simp only [Prod.snd_mul, Prod.fst_mul, mul_inv]
    ac_rfl
  refine Prod.ext (Subtype.ext (funext fun i => ?_)) (Subtype.ext (funext fun i => ?_))
  · simp [bAct, Um.scale, mul_assoc]
  · fin_cases i
    · simp only [bAct, Um.scale]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [e, Units.val_mul, mul_assoc]
    · simp [bAct, Um.scale, mul_assoc]

theorem bAct_map {N : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : Aˣ × Aˣ) (x : Um N A × Um 2 A) :
    ((Um.map N f).obj (bAct g x).1, (Um.map 2 f).obj (bAct g x).2) =
      bAct (Units.map (f : A →* B) g.1, Units.map (f : A →* B) g.2) ((Um.map N f).obj x.1, (Um.map 2 f).obj x.2) := by
  refine Prod.ext (Um.map_scale f _ x.1) (Subtype.ext (funext fun i => ?_))
  fin_cases i <;> simp [bAct, Um.scale, Um.map]

def bD (N : ℕ) : CommRingCat.{0} ⥤ Type where
  obj A := Um N A × Um 2 A
  map f := TypeCat.ofHom fun x => ((Um.map N f.hom).obj x.1, (Um.map 2 f.hom).obj x.2)
  map_id A := by
    ext x <;> rfl
  map_comp f g := by
    ext x <;> rfl

def gm2F : CommRingCat.{0} ⥤ GrpCat.{0} where
  obj A := GrpCat.of (Aˣ × Aˣ)
  map f := GrpCat.ofHom (MonoidHom.prodMap (Units.map (f.hom : _ →* _)) (Units.map (f.hom : _ →* _)))
  map_id A := by ext <;> rfl
  map_comp f g := by ext <;> rfl

def BC (N : ℕ) : Act where
  D := bD N
  G := gm2F
  smul A g x := bAct (A := A) g x
  one_smul A x := bAct_one (A := A) x
  mul_smul A g h x := bAct_mul (A := A) g h x
  nat f g x := bAct_map f.hom g x

def Um.join {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A) : Um (N + 1) A :=
  ⟨Fin.snoc (α := fun _ => A) (fun i => x.2.1 0 * x.1.1 i) (x.2.1 1), by
    set I := Ideal.span (Set.range (Fin.snoc (α := fun _ => A) (fun i => x.2.1 0 * x.1.1 i) (x.2.1 1))) with hI
    have h0 : ∀ y ∈ Ideal.span (Set.range x.1.1), x.2.1 0 * y ∈ I := fun y hy => by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, rfl⟩
        refine Ideal.subset_span ⟨Fin.castSucc i, ?_⟩
        simp
      · simp
      · intro a b _ _ ha hb
        rw [mul_add]
        exact I.add_mem ha hb
      · intro r a _ ha
        rw [smul_eq_mul, mul_left_comm]
        exact I.mul_mem_left r ha
    have h1 : x.2.1 1 ∈ I := Ideal.subset_span ⟨Fin.last N, by simp⟩
    refine top_le_iff.1 (le_trans (le_of_eq x.2.2.symm) (Ideal.span_le.2 ?_))
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · have := h0 1 (by rw [x.1.2]; trivial)
      simpa using this
    · exact h1⟩

theorem Um.join_map {N : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Um N A × Um 2 A) :
    Um.join ((Um.map N f).obj x.1, (Um.map 2 f).obj x.2) = (Um.map (N + 1) f).obj (Um.join x) := by
  refine Subtype.ext (funext fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Um.join, Um.map]

theorem Um.join_bAct {N : ℕ} {A : Type} [CommRing A] (u : Aˣ × Aˣ) (x : Um N A × Um 2 A) :
    Um.join (bAct u x) = Um.scale (fun _ => u.2) (Um.join x) := by
  refine Subtype.ext (funext fun j => ?_)
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [Um.join, bAct, Um.scale]
  · have hu : ((u.1⁻¹ : Aˣ) : A) * (u.1 : A) = 1 := Units.inv_mul u.1
    simp only [Um.join, bAct, Um.scale, Fin.snoc_castSucc, Matrix.cons_val_zero]
    calc ((↑(u.2 * u.1⁻¹) : A) * x.2.1 0) * ((u.1 : A) * x.1.1 i)
        = (u.2 : A) * (((u.1⁻¹ : Aˣ) : A) * (u.1 : A)) * (x.2.1 0 * x.1.1 i) := by
          rw [Units.val_mul]
          ring
      _ = (u.2 : A) * (x.2.1 0 * x.1.1 i) := by rw [hu, mul_one]

def pC (N : ℕ) : Act.Hom (BC N) (XC N) where
  d := { app := fun A => TypeCat.ofHom fun x => x.1, naturality := fun _ _ _ => rfl }
  g := { app := fun A => GrpCat.ofHom (MonoidHom.fst _ _), naturality := fun _ _ _ => rfl }
  eq _ _ _ := rfl

def βC (N : ℕ) : Act.Hom (BC N) (XC (N + 1)) where
  d :=
    { app := fun A => TypeCat.ofHom Um.join
      naturality := fun A B f => by
        ext x
        exact Um.join_map f.hom x }
  g := { app := fun A => GrpCat.ofHom (MonoidHom.snd _ _), naturality := fun _ _ _ => rfl }
  eq A u x := Um.join_bAct (A := A) u x

def chiX (M : ℕ) : (XC M).G ⟶ gmF := 𝟙 gmF

def chiB (N : ℕ) : (BC N).G ⟶ gmF := (βC N).g ≫ chiX (N + 1)

def chiH (N : ℕ) : (BC N).G ⟶ gmF := (pC N).g ≫ chiX N

def unitAt {M : ℕ} (i : Fin M) : Pred (XC M) where
  P A v := IsUnit ((show Um M A from v).1 i)
  map f v h := h.map f.hom
  smul A g v := by
    change IsUnit (((show Aˣ from g) : A) * (show Um M A from v).1 i) ↔ _
    exact Units.isUnit_units_mul _ _

theorem span_scale {M : ℕ} {A : Type} [CommRing A] (u : Aˣ) (w : Fin M → A) (S : Set (Fin M)) :
    Ideal.span ((fun i => (u : A) * w i) '' S) = Ideal.span (w '' S) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, hi, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have e : w i = ((u⁻¹ : Aˣ) : A) * ((u : A) * w i) := by simp
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, hi, rfl⟩)

def spanOn {M : ℕ} (S : Set (Fin M)) : Pred (XC M) where
  P A v := Ideal.span ((show Um M A from v).1 '' S) = ⊤
  map {A B} f v h := by
    have e := congrArg (Ideal.map f.hom) h
    rw [Ideal.map_span, Ideal.map_top, ← Set.image_comp] at e
    exact e
  smul A g v := Eq.congr_left (span_scale (A := A) g (show Um M A from v).1 S)

abbrev Q1 (N : ℕ) : Pred (XC (N + 1)) := unitAt (Fin.last N)

abbrev Q2 (N : ℕ) : Pred (XC (N + 1)) := spanOn (Set.range Fin.castSucc)

def Pbf (q : ℕ) (S : Spc) (M : ℕ) : Prop :=
  LH q (Sp.fst S (XC M)) (fun j : Fin M => 2 * (((j : ℕ) : ℤ))) (fun j : Fin M => ((j : ℕ) : ℤ))
    (fun j => cpow q (c1 q (Sp.line S (chiX M))) j)

def LHQ (q : ℕ) (E : Spc) {c a : Act} (π : Act.Hom c a) {m : ℕ} (d e : Fin m → ℤ) (cl : ∀ j, Ht q (Sp E c) (d j) (e j))
    (Q : Pred a) : Prop :=
  LH q (Sp.map E (π.sub Q)) d e (fun j => pull _ (Sp.map E (incl (Q.comap π))) _ _ (cl j))

end UpperTheory.Blow

end
