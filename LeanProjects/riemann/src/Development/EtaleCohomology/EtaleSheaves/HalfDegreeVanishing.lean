import Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing.SecondBlockUnimodularLocusInclusionMono

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.HalfDegreeVanishing

theorem um_hom_val {N : ℕ} {A : Type} [CommRing A] {v w v' w' : Um N A} (hv : v = v') (hw : w = w') (p : v' ⟶ w') :
    (eqToHom hv ≫ p ≫ eqToHom hw.symm).1 = p.1 := by
  subst hv hw; simp

theorem um_functor_ext {N n : ℕ} {A : Type} [CommRing A] (F G : Fin (n + 1) ⥤ Um N A)
    (ho : ∀ i, (F.obj i).1 = (G.obj i).1) (hm : ∀ {i j : Fin (n + 1)} (f : i ⟶ j), (F.map f).1 = (G.map f).1) : F = G := by
  refine CategoryTheory.Functor.ext (fun i => Subtype.ext (ho i)) (fun i j f => ?_)
  apply Subtype.ext
  exact (hm f).trans (um_hom_val (Subtype.ext (ho i)) (Subtype.ext (ho j)) (G.map f)).symm

variable {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b))

theorem arrow_eq {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W (pe V W x)).map f).val.mulVec (wb (a := a) ((pv V W x).obj i).1) =
      (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) • wb (a := a) ((pv V W x).obj j).1 := by
  have e := ((pv V W x).map f).2
  rw [cond] at e
  have e2 := congrArg (wb (a := a)) e
  rw [wb_mulVec] at e2
  exact e2

def gfun {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) (hx : AllSec V W x) :
    Fin (n + 1) ⥤ Um b (Scheme.Γ.obj (op X)) where
  obj i := ⟨wb (a := a) ((pv V W x).obj i).1, hx i⟩
  map {i j} f := ⟨((pw W (pe V W x)).map f, ((pv V W x).map f).1.2), arrow_eq V W x f⟩
  map_id i := Subtype.ext (Prod.ext ((pw W (pe V W x)).map_id i) (congrArg (fun p => p.1.2) ((pv V W x).map_id i)))
  map_comp f g := Subtype.ext (Prod.ext ((pw W (pe V W x)).map_comp f g) (congrArg (fun p => p.1.2) ((pv V W x).map_comp f g)))

theorem pe_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) :
    pe V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) = (E.obj (op (SimplexCategory.mk n))).map k.op (pe V W x) :=
  ConcreteCategory.congr_hom (((pullback.fst (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).naturality k.op) x

theorem pw_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (e : Sx E n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op Y)) from (pw W ((E.obj (op (SimplexCategory.mk n))).map k.op e)).map f) =
      Matrix.GeneralLinearGroup.map (Scheme.Γ.map k.op).hom (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W e).map f) :=
  eq_of_heq (Functor.hcongr_hom (ConcreteCategory.congr_hom ((W.app (op (SimplexCategory.mk n))).naturality k.op) e) f)

end LateralTheory.E.HalfDegreeVanishing
