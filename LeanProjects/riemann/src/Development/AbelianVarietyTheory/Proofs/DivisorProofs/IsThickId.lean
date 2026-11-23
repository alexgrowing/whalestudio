import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.LBLift

section Alg

variable {R : Type} [CommRing R] (I : Ideal R) {D T : Type} [Category.{0} D] [Category.{0} T]

def In1 (F : D ⥤ CommAlgCat.{0} R) (f : C1 F) : Prop :=
  ∀ (t t' : D) (a : t ⟶ t'), f t t' a ∈ I.map (algebraMap R (F.obj t'))

def In2 (F : D ⥤ CommAlgCat.{0} R) (z : C2 F) : Prop :=
  ∀ (t t' t'' : D) (a : t ⟶ t') (b : t' ⟶ t''), z t t' t'' a b ∈ I.map (algebraMap R (F.obj t''))

variable {F : D ⥤ CommAlgCat.{0} R} {F' : T ⥤ CommAlgCat.{0} R}

def PrimI (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F') : Prop :=
  ∀ (z : Z2 F) (f : C1 F'), In2 I F z.1 → In1 I F' f →
    d1 F' f = (n₀.pullbackTwoCocycle z).1 - (n₁.pullbackTwoCocycle z).1 - (n₂.pullbackTwoCocycle z).1 → ∃ f₀ : C1 F, In1 I F f₀ ∧ d1 F f₀ = z.1

def mdef (F : D ⥤ CommAlgCat.{0} R) (u : C1 F) : C2 F :=
  fun t t' t'' a b ↦ mp F b (u t t' a) * u t' t'' b - u t t'' (a ≫ b)

def MulRel (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F') (u : C1 F) (v : C0 F') : Prop :=
  In1 I F' fun t t' a ↦ n₀.α t' (u _ _ (n₀.G.map a)) * v t' -
    n₁.α t' (u _ _ (n₁.G.map a)) * n₂.α t' (u _ _ (n₂.G.map a)) * mp F' a (v t)

end Alg

section Geo

variable {R : Type} [CommRing R] {X X₀ Y : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

structure IsBasis (G : D ⥤ AffOp X) : Prop where
  cover : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : D, x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U
  dir : ∀ (t₁ t₂ : D) (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 →
    ∃ t₃ : D, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U

def pullMap {s : X ⟶ Sp R} {s' : Y ⟶ Sp R} {φ : Y ⟶ X} (w : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (G : D ⥤ AffOp X) (H : T ⥤ AffOp Y) (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) :
    CoefMap (RingHom.id R) (G ⋙ OAff s) (H ⋙ OAff s') where
  G := K
  α t := CechDR.secPull s s' ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩
  naturality {p q} a b :=
    (congrArg (fun t ↦ t.hom b) (φ.map_appLE (le q) (homOfLE (leOfHom (G.map (K.map a)).unop)).op)).trans
      (congrArg (fun t ↦ t.hom b) (φ.appLE_map (le p) (homOfLE (leOfHom (H.map a).unop)).op)).symm
  smul t := semiHom_secPull w ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩

structure IsThick (I : Ideal R) (s : X ⟶ Sp R) (i : X₀ ⟶ X) : Prop where
  closed : IsClosedImmersion i
  surj : Surjective i
  app_surj : ∀ U : X.affineOpens, Function.Surjective (i.app U.1).hom
  ker : ∀ (U : X.affineOpens) (b : Sec s U.1), (i.app U.1).hom b = 0 ↔ b ∈ I.map (algebraMap R (Sec s U.1))

def Small (i : X₀ ⟶ X) (L : LB X₀) : Type := {p : X.affineOpens × L.ι // i ⁻¹ᵁ p.1.1 ≤ L.U p.2}

instance (i : X₀ ⟶ X) (L : LB X₀) : Preorder (Small i L) := Preorder.lift fun p ↦ p.1.1

def smallG (i : X₀ ⟶ X) (L : LB X₀) : (Small i L)ᵒᵖ ⥤ AffOp X :=
  (Monotone.functor (f := fun p : Small i L ↦ p.1.1) fun _ _ h ↦ h).op

theorem Small.le_inf {i : X₀ ⟶ X} {L : LB X₀} {p q : (Small i L)ᵒᵖ} (a : p ⟶ q) :
    i ⁻¹ᵁ q.unop.1.1.1 ≤ L.U p.unop.1.2 ⊓ L.U q.unop.1.2 :=
  _root_.le_inf (fun _ hx ↦ p.unop.2 ((show q.unop.1.1 ≤ p.unop.1.1 from leOfHom a.unop) hx)) q.unop.2

def IsLift (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀) (u : C1 (smallG i L ⋙ OAff s)) : Prop :=
  ∀ (p q : (Small i L)ᵒᵖ) (a : p ⟶ q),
    (i.app q.unop.1.1.1).hom (u p q a) = (res (Small.le_inf a) (L.g p.unop.1.2 q.unop.1.2)).val

end Geo

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CechPic in
attribute [local instance] Over.cartesianMonoidalCategory in

def AbLift : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (X₀ Y₀ : Scheme.{0}) (i : X₀ ⟶ A.left) (i' : Y₀ ⟶ (A ⊗ A).left) (ψ₀ ψ₁ ψ₂ : Y₀ ⟶ X₀),
      IsThick I A.hom i → IsThick I (A ⊗ A).hom i' → ψ₀ ≫ i = i' ≫ (μ[A]).left → ψ₁ ≫ i = i' ≫ (fst A A).left →
      ψ₂ ≫ i = i' ≫ (snd A A).left →
      ∀ c : Pic X₀, CechPic.pull ψ₀ c = CechPic.pull ψ₁ c + CechPic.pull ψ₂ c → ∃ c' : Pic A.left, CechPic.pull i c' = c

end GlobalTheory.LBLift
