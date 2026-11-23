import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoTors

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

abbrev sq : A ⟶ A := (𝟙 A) ^ 2

theorem comp_sq {T : Over S} (x : T ⟶ A) : x ≫ sq A = x ^ 2 := by
  rw [sq, MonObj.comp_pow, Category.comp_id]

abbrev Two : Over S := pullback (sq A) η[A]

abbrev incl : Two A ⟶ A := pullback.fst _ _

variable {A}

theorem incl_sq {T : Over S} (u : T ⟶ Two A) : (u ≫ incl A) ^ 2 = 1 := by
  rw [← comp_sq, Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

def kpt {T : Over S} (x : T ⟶ A) (hx : x ^ 2 = 1) : T ⟶ Two A :=
  pullback.lift x (toUnit _) (by rw [comp_sq, hx, Hom.one_def])

@[simp, reassoc] theorem kpt_incl {T : Over S} (x : T ⟶ A) (hx : x ^ 2 = 1) : kpt x hx ≫ incl A = x :=
  pullback.lift_fst _ _ _

theorem two_ext {T : Over S} {u v : T ⟶ Two A} (h : u ≫ incl A = v ≫ incl A) : u = v :=
  pullback.hom_ext h (toUnit_unique _ _)

variable (A)

def twoFun : (Over S)ᵒᵖ ⥤ CommGrpCat.{0} where
  obj T := CommGrpCat.of (MonoidHom.ker (powMonoidHom 2 : (Opposite.unop T ⟶ A) →* (Opposite.unop T ⟶ A)))
  map φ := CommGrpCat.ofHom
    { toFun := fun x => ⟨φ.unop ≫ x.1, by
        show (φ.unop ≫ x.1) ^ 2 = 1
        rw [← MonObj.comp_pow, show x.1 ^ 2 = 1 from x.2, MonObj.comp_one]⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := by ext x; exact Category.id_comp _
  map_comp φ ψ := by ext x; exact Category.assoc _ _ _

def twoRep : (twoFun A ⋙ forget _).RepresentableBy (Two A) where
  homEquiv {T} :=
    { toFun := fun u => (⟨u ≫ incl A, incl_sq u⟩ : MonoidHom.ker (powMonoidHom 2 : (T ⟶ A) →* (T ⟶ A)))
      invFun := fun x => kpt x.1 x.2
      left_inv := fun u => two_ext (kpt_incl _ _)
      right_inv := fun x => Subtype.ext (kpt_incl _ _) }
  homEquiv_comp {T T'} f u := Subtype.ext (Category.assoc _ _ _)

instance : CommGrpObj (Two A) := CommGrpObj.ofRepresentableBy _ (twoFun A) (twoRep A)

variable {A}

theorem mul_incl {T : Over S} (x y : T ⟶ Two A) : (x * y) ≫ incl A = (x ≫ incl A) * (y ≫ incl A) := by
  have h := ((yonedaGrpObjIsoOfRepresentableBy (Two A) (twoFun A ⋙ forget₂ CommGrpCat GrpCat)
    (twoRep A)).hom.app (Opposite.op T)).hom.map_mul x y
  exact congrArg Subtype.val h

end GlobalTheory.TwoTors

namespace GlobalTheory.TwoTors

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

theorem sq_w : (sq A).left ≫ A.hom = A.hom := Over.w _

abbrev pairO : Over S := Over.mk (pullback.fst (sq A).left (sq A).left ≫ A.hom)

abbrev tripO : Over S :=
  Over.mk (pullback.fst _ _ ≫ pullback.fst (sq A).left (sq A).left ≫ A.hom :
    GlobalTheory.LBDescent.Triple (sq A).left ⟶ S)

theorem snd_w : pullback.snd (sq A).left (sq A).left ≫ A.hom = pullback.fst (sq A).left (sq A).left ≫ A.hom := by
  rw [← sq_w A, pullback.condition_assoc]

def s₁ : pairO A ⟶ A := Over.homMk (pullback.fst _ _) rfl

def s₂ : pairO A ⟶ A := Over.homMk (pullback.snd _ _) (snd_w A)

theorem s_sq : s₁ A ≫ sq A = s₂ A ≫ sq A := Over.OverMorphism.ext pullback.condition

def t₁ : tripO A ⟶ A := Over.homMk (pullback.fst _ _ ≫ pullback.fst _ _) rfl

def t₂ : tripO A ⟶ A := Over.homMk (pullback.fst _ _ ≫ pullback.snd _ _) (by
  show (pullback.fst _ _ ≫ pullback.snd _ _) ≫ A.hom = _
  rw [Category.assoc, snd_w]; rfl)

def t₃ : tripO A ⟶ A := Over.homMk (pullback.snd _ _ ≫ pullback.snd _ _) (by
  show (pullback.snd _ _ ≫ pullback.snd _ _) ≫ A.hom = _
  rw [Category.assoc, snd_w, ← pullback.condition_assoc, snd_w]; rfl)

theorem t₁₂_sq : t₁ A ≫ sq A = t₂ A ≫ sq A :=
  Over.OverMorphism.ext (by
    show (pullback.fst _ _ ≫ pullback.fst _ _) ≫ (sq A).left = (pullback.fst _ _ ≫ pullback.snd _ _) ≫ (sq A).left
    rw [Category.assoc, Category.assoc, pullback.condition])
theorem t₂₃_sq : t₂ A ≫ sq A = t₃ A ≫ sq A :=
  Over.OverMorphism.ext (by
    show (pullback.fst _ _ ≫ pullback.snd _ _) ≫ (sq A).left = (pullback.snd _ _ ≫ pullback.snd _ _) ≫ (sq A).left
    simp only [Category.assoc]
    have e := pullback.condition (f := pullback.snd (sq A).left (sq A).left) (g := pullback.fst (sq A).left (sq A).left)
    rw [reassoc_of% e, pullback.condition])

variable {A}

def dif {T : Over S} (a b : T ⟶ A) (h : a ≫ sq A = b ≫ sq A) : T ⟶ Two A :=
  kpt (a⁻¹ * b) (by rw [mul_pow, inv_pow, ← comp_sq, ← comp_sq, h, inv_mul_cancel])

@[simp, reassoc] theorem dif_incl {T : Over S} (a b : T ⟶ A) (h : a ≫ sq A = b ≫ sq A) :
    dif a b h ≫ incl A = a⁻¹ * b := kpt_incl _ _

variable (A)

def ψ : tripO A ⟶ Two A ⊗ Two A := lift (dif (t₁ A) (t₂ A) (t₁₂_sq A)) (dif (t₂ A) (t₃ A) (t₂₃_sq A))

def δ : pairO A ⟶ Two A := dif (s₁ A) (s₂ A) (s_sq A)

end GlobalTheory.TwoTors
