import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KummerSplit

def unitsT : CommRingCat.{0} ⥤ Type where
  obj A := (A : Type)ˣ
  map {A B} f := TypeCat.ofHom fun (u : (A : Type)ˣ) => Units.map f.hom.toMonoidHom u
  map_id A := by ext u; rfl
  map_comp f g := by ext u; rfl

structure Trip (q : ℕ) (A : Type) [CommRing A] where
  root : Prim q A
  src : Aˣ
  tgt : Aˣ
  tgt_eq : (tgt : A) = root.1 * src

def Trip.map {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Trip q A) : Trip q B :=
  ⟨x.root.map f, Units.map f.toMonoidHom x.src, Units.map f.toMonoidHom x.tgt, by
    change f (x.tgt : A) = f x.root.1 * f (x.src : A)
    rw [x.tgt_eq, map_mul]⟩

def tripT (q : ℕ) : CommRingCat.{0} ⥤ Type where
  obj A := Trip q A
  map f := TypeCat.ofHom (Trip.map f.hom)
  map_id A := by
    ext x
    cases x
    rfl
  map_comp f g := by
    ext x
    cases x
    rfl

def unitsP : PSh := Scheme.Γ ⋙ unitsT

def tripP (q : ℕ) : PSh := Scheme.Γ ⋙ tripT q

def unitsP.mk {U : Scheme.{0}} (v : (Γ(U, ⊤))ˣ) : unitsP.obj (op U) := v

def tripP.mk {q : ℕ} {U : Scheme.{0}} (x : Trip q Γ(U, ⊤)) : (tripP q).obj (op U) := x

def tripP.get {q : ℕ} {U : Scheme.{0}} (x : (tripP q).obj (op U)) : Trip q Γ(U, ⊤) := x

theorem unitsP.map_mk {V U : Scheme.{0}} (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ) :
    unitsP.map g.op (unitsP.mk v) = unitsP.mk (Units.map g.appTop.hom.toMonoidHom v) := rfl

theorem tripP.get_map {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : (tripP q).obj (op U)) :
    tripP.get ((tripP q).map g.op x) = (tripP.get x).map g.appTop.hom := rfl

theorem smap_sum {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type} (c : ι →₀ ULift.{1} R) (f : ι → Sec F U) :
    Sec.map φ (c.sum fun x r => r • f x) = c.sum fun x r => r • Sec.map φ (f x) := by
  simp only [Sec.map, map_finsuppSum, map_smul]

theorem res_sum {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) {ι : Type} (c : ι →₀ ULift.{1} R) (f : ι → Sec F U) :
    Sec.res g (c.sum fun x r => r • f x) = c.sum fun x r => r • Sec.res g (f x) := by
  simp only [Sec.res, map_finsuppSum, map_smul]

theorem smap_sub {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := map_sub _ _ _

theorem res_sub {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _

theorem res_zero' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem smap_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem sec_eq_zero_of_loc {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (s : Sec F U)
    (h : Loc U fun _ g => Sec.res g s = 0) : s = 0 := by
  obtain ⟨S, hS, hS'⟩ := h
  exact Sheaf.isSeparated F U S hS s 0 (fun V g hg => (hS' V g hg).trans (map_zero _).symm)

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change ((φ.hom.app (op U)) ≫ G.obj.map g.op).hom x = (F.obj.map g.op ≫ φ.hom.app (op V)).hom x
  rw [φ.hom.naturality]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

end GlobalTheory.EtC.KummerSplit
