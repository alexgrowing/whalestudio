import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ConeEl

variable {T : Type 1} [Category.{0} T] {C D : T ⥤ AbCx} (φ : C ⟶ D)

def coneD (U : T) (n : ℤ) :
    AddCommGrpCat.of ((C.obj U).X (n + 1) × (D.obj U).X n) ⟶
      AddCommGrpCat.of ((C.obj U).X (n + 1 + 1) × (D.obj U).X (n + 1)) :=
  AddCommGrpCat.ofHom
    { toFun := fun x => (-(C.obj U).d (n + 1) (n + 1 + 1) x.1,
        (φ.app U).f (n + 1) x.1 + (D.obj U).d n (n + 1) x.2)
      map_zero' := by simp
      map_add' := fun x y => by
        refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, map_add, neg_add] <;> abel }

lemma coneD_apply (U : T) (n : ℤ) (x : (C.obj U).X (n + 1) × (D.obj U).X n) :
    coneD φ U n x = (-(C.obj U).d (n + 1) (n + 1 + 1) x.1,
        (φ.app U).f (n + 1) x.1 + (D.obj U).d n (n + 1) x.2) := rfl

lemma dd_apply (K : AbCx) (i j k : ℤ) (x : K.X i) : K.d j k (K.d i j x) = 0 := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]; rfl

lemma comm_apply {K L : AbCx} (f : K ⟶ L) (i j : ℤ) (x : K.X i) : f.f j (K.d i j x) = L.d i j (f.f i x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm]

lemma coneD_sq (U : T) (n : ℤ) : coneD φ U n ≫ coneD φ U (n + 1) = 0 := by
  refine AddCommGrpCat.ext fun x => ?_
  change coneD φ U (n + 1) (coneD φ U n x) = 0
  rw [coneD_apply, coneD_apply]
  refine Prod.ext ?_ ?_
  · simp [dd_apply]
  · simp [dd_apply, comm_apply]

def coneObj (U : T) : AbCx :=
  CochainComplex.of (fun n => AddCommGrpCat.of ((C.obj U).X (n + 1) × (D.obj U).X n)) (coneD φ U) (coneD_sq φ U)

lemma nat_apply {U V : T} (g : U ⟶ V) (n : ℤ) (x : (C.obj U).X n) :
    (D.map g).f n ((φ.app U).f n x) = (φ.app V).f n ((C.map g).f n x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, φ.naturality]

def coneMap {U V : T} (g : U ⟶ V) : coneObj φ U ⟶ coneObj φ V :=
  CochainComplex.ofHom (X := coneObj φ U) (Y := coneObj φ V)
    (fun n => AddCommGrpCat.ofHom (AddMonoidHom.prodMap ((C.map g).f (n + 1)).hom ((D.map g).f n).hom))
    (fun n => by
      refine AddCommGrpCat.ext fun x => ?_
      simp only [coneObj, CochainComplex.of_d]
      change coneD φ V n (((C.map g).f (n + 1)) x.1, ((D.map g).f n) x.2) =
        (((C.map g).f (n + 1 + 1)) (coneD φ U n x).1, ((D.map g).f (n + 1)) (coneD φ U n x).2)
      rw [coneD_apply]
      erw [coneD_apply]
      refine Prod.ext ?_ ?_
      · simp [comm_apply]
      · simp [comm_apply, nat_apply])

@[simp] lemma coneMap_f_apply {U V : T} (g : U ⟶ V) (n : ℤ) (x : (coneObj φ U).X n) :
    (coneMap φ g).f n x = ((C.map g).f (n + 1) x.1, (D.map g).f n x.2) := rfl

def cone : T ⥤ AbCx where
  obj := coneObj φ
  map := coneMap φ
  map_id U := by
    ext n x
    refine Prod.ext ?_ ?_
    · change (C.map (𝟙 U)).f (n + 1) x.1 = x.1
      rw [CategoryTheory.Functor.map_id]; rfl
    · change (D.map (𝟙 U)).f n x.2 = x.2
      rw [CategoryTheory.Functor.map_id]; rfl
  map_comp f g := by
    ext n x
    refine Prod.ext ?_ ?_
    · change (C.map (f ≫ g)).f (n + 1) x.1 = (C.map g).f (n + 1) ((C.map f).f (n + 1) x.1)
      rw [CategoryTheory.Functor.map_comp]; rfl
    · change (D.map (f ≫ g)).f n x.2 = (D.map g).f n ((D.map f).f n x.2)
      rw [CategoryTheory.Functor.map_comp]; rfl

def coneFst (n : ℤ) : term (cone φ) n ⟶ term C (n + 1) where
  app U := AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)
  naturality U V g := rfl

def coneSnd (n : ℤ) : term (cone φ) n ⟶ term D n where
  app U := AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)
  naturality U V g := rfl

end GlobalTheory.EtC.ConeEl

open GlobalTheory.EtC.ConeEl in

theorem GlobalTheory.EtC.coneEl_exists : ∀ (T : Type 1) [Category.{0} T] (C D : T ⥤ AbCx) (φ : C ⟶ D), ∃ (K : T ⥤ AbCx) (p : ∀ n : ℤ, term K n ⟶ term C (n + 1)) (q : ∀ n : ℤ, term K n ⟶ term D n), (∀ n U, Function.Bijective (fun x : (K.obj U).X n => ((p n).app U x, (q n).app U x))) ∧ ∀ n U (x : (K.obj U).X n), (p (n + 1)).app U ((K.obj U).d n (n + 1) x) = - (C.obj U).d (n + 1) (n + 1 + 1) ((p n).app U x) ∧ (q (n + 1)).app U ((K.obj U).d n (n + 1) x) = (φ.app U).f (n + 1) ((p n).app U x) + (D.obj U).d n (n + 1) ((q n).app U x) := by
  intro T _ C D φ
  refine ⟨cone φ, coneFst φ, coneSnd φ, fun n U => ?_, fun n U x => ?_⟩
  · refine ⟨fun x y h => ?_, fun y => ⟨(y.1, y.2), rfl⟩⟩
    exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  · have hd : (cone φ |>.obj U).d n (n + 1) = coneD φ U n := CochainComplex.of_d (fun n => AddCommGrpCat.of ((C.obj U).X (n + 1) × (D.obj U).X n)) (coneD φ U) n
    constructor
    · change ((cone φ |>.obj U).d n (n + 1) x).1 = _
      rw [hd]; rfl
    · change ((cone φ |>.obj U).d n (n + 1) x).2 = _
      rw [hd]; rfl
