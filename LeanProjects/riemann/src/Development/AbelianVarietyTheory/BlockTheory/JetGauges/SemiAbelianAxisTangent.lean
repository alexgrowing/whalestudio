import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section At

variable {X : Scheme.{0}} {S : Type} [CommRing S]

def jetAdd (d m : ℕ) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m :=
  jetMap (fun p => MvPolynomial.X ((0 : Fin 2), p.2) + MvPolynomial.X ((1 : Fin 2), p.2))
    fun _ => Ideal.add_mem _ (X_mem_orig _) (X_mem_orig _)

abbrev JetFamily (G : Over X) (x0 : Sp S ⟶ X) (d : ℕ) : Type :=
  ∀ m : ℕ, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ G

variable {G : Over X} {x0 : Sp S ⟶ X} {d : ℕ}

def axisTangent (x : JetFamily G x0 d) (j : Fin d) : overAt x0 (DualNumber S) ⟶ G :=
  homAt x0 (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1

def SameTangents (x x' : JetFamily G x0 d) : Prop :=
  ∀ j : Fin d, axisTangent x j = axisTangent x' j

structure IsAdditiveHom [GrpObj G] (x : JetFamily G x0 d) : Prop where
  trunc : ∀ m, homAt x0
    (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) ≫ x (m + 1) = x m
  zero : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1
  add : ∀ m, homAt x0 (jetAdd d m) ≫ x m =
    (homAt x0 (jetCopy d m (0 : Fin 2)) ≫ x m) * (homAt x0 (jetCopy d m (1 : Fin 2)) ≫ x m)

end At

def UniqueAtBasePoint : Prop :=
  ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G]
    (S : Type) [CommRing S] [Algebra ℚ S] (x0 : Sp S ⟶ X) (d : ℕ) (x x' : JetFamily G x0 d),
    IsAdditiveHom x → IsAdditiveHom x' → SameTangents x x' → ∀ m, x m = x' m

def UniqueAtBasePointSemiAbelian : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X)
    (S : Type) [CommRing S] [Algebra ℚ S] (x0 : Sp S ⟶ X) (d : ℕ) (x x' : JetFamily t.G x0 d),
    IsAdditiveHom x → IsAdditiveHom x' → SameTangents x x' → ∀ m, x m = x' m

def UniqueAtFramedPoint : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (d : ℕ) (x x' : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G),
    IsAdditiveHom (x0 := y.x) x → IsAdditiveHom (x0 := y.x) x' → SameTangents (x0 := y.x) x x' →
      ∀ m, x m = x' m

def ExpUnique : Prop := UniqueAtBasePoint ∧ UniqueAtFramedPoint

section Model

def vecFunctor (X : Scheme.{0}) (d : ℕ) : (Over X)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (Multiplicative (Fin d → Γ(T.unop.left, ⊤)))
  map g := GrpCat.ofHom (MonoidHom.mk' (fun v => Multiplicative.ofAdd fun j => g.unop.left.appTop.hom (v.toAdd j))
    fun v w => funext fun j => map_add g.unop.left.appTop.hom (v.toAdd j) (w.toAdd j))
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun v => funext fun j =>
    congrArg (fun q => q.hom (v.toAdd j)) (Scheme.Hom.id_appTop (X := T.unop.left)))
  map_comp g g' := GrpCat.hom_ext (MonoidHom.ext fun x => rfl)

def vecObj (X : Scheme.{0}) (d : ℕ) : Over X := Over.mk (𝔸(Fin d; X) ↘ X)

def vecEquiv {X : Scheme.{0}} {d : ℕ} (T : Over X) :
    (T ⟶ vecObj X d) ≃ Multiplicative (Fin d → Γ(T.left, ⊤)) where
  toFun x := Multiplicative.ofAdd fun j => x.left.appTop (AffineSpace.coord X j)
  invFun v := Over.homMk (AffineSpace.homOfVector T.hom v.toAdd) (AffineSpace.homOfVector_over _ _)
  left_inv x := Over.OverMorphism.ext (AffineSpace.hom_ext
    ((AffineSpace.homOfVector_over _ _).trans (Over.w x).symm) fun i =>
      AffineSpace.homOfVector_appTop_coord _ _ i)
  right_inv v := funext fun j => AffineSpace.homOfVector_appTop_coord _ _ j

def vecRep (X : Scheme.{0}) (d : ℕ) : (vecFunctor X d ⋙ forget _).RepresentableBy (vecObj X d) where
  homEquiv {T} := vecEquiv T
  homEquiv_comp _ _ := rfl

instance (X : Scheme.{0}) (d : ℕ) : GrpObj (vecObj X d) := GrpObj.ofRepresentableBy _ _ (vecRep X d)

theorem vecEquiv_mul {X : Scheme.{0}} {d : ℕ} {T : Over X} (x y : T ⟶ vecObj X d) :
    vecEquiv T (x * y) = vecEquiv T x * vecEquiv T y :=
  ((yonedaGrpObjIsoOfRepresentableBy _ _ (vecRep X d)).hom.app (Opposite.op T)).hom.map_mul x y

theorem vecEquiv_one {X : Scheme.{0}} {d : ℕ} {T : Over X} :
    vecEquiv T (1 : T ⟶ vecObj X d) = 1 :=
  ((yonedaGrpObjIsoOfRepresentableBy _ _ (vecRep X d)).hom.app (Opposite.op T)).hom.map_one

instance (X : Scheme.{0}) (d : ℕ) : IsCommMonObj (vecObj X d) where
  mul_comm := by
    have h : fst (vecObj X d) (vecObj X d) * snd (vecObj X d) (vecObj X d) =
        snd (vecObj X d) (vecObj X d) * fst (vecObj X d) (vecObj X d) :=
      (vecEquiv _).injective (by rw [vecEquiv_mul, vecEquiv_mul, _root_.mul_comm])
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [← lift_snd_fst]
    exact h.symm

variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) (d : ℕ)

def vecPt {A : Type} [CommRing A] [Algebra S A] (v : Fin d → A) : overAt x0 A ⟶ vecObj X d :=
  (vecEquiv (overAt x0 A)).symm (Multiplicative.ofAdd fun j => toΓ A (v j))

theorem homAt_vecPt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B]
    (f : A →ₐ[S] B) (v : Fin d → A) : homAt x0 f ≫ vecPt x0 d v = vecPt x0 d fun j => f (v j) := by
  apply (vecEquiv _).injective
  have h : vecEquiv _ (homAt x0 f ≫ vecPt x0 d v) = Multiplicative.ofAdd fun j =>
      (spMap (f : A →+* B)).appTop.hom ((vecEquiv _ (vecPt x0 d v)).toAdd j) := rfl
  rw [h, vecPt, vecPt, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  congr 1
  funext j
  exact congrArg (fun q => q.hom (v j))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (f : A →+* B))).symm

theorem vecPt_add {A : Type} [CommRing A] [Algebra S A] (v w : Fin d → A) :
    vecPt x0 d (v + w) = vecPt x0 d v * vecPt x0 d w := by
  apply (vecEquiv _).injective
  rw [vecEquiv_mul, vecPt, vecPt, vecPt, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact funext fun j => map_add (toΓ A) (v j) (w j)

theorem vecPt_zero {A : Type} [CommRing A] [Algebra S A] : vecPt x0 d (0 : Fin d → A) = 1 := by
  apply (vecEquiv _).injective
  rw [vecEquiv_one, vecPt, Equiv.apply_symm_apply]
  exact funext fun j => map_zero (toΓ A)

theorem vecPt_injective {A : Type} [CommRing A] [Algebra S A] :
    Function.Injective (vecPt x0 d : (Fin d → A) → _) := fun v w h => by
  have h' := (vecEquiv (overAt x0 A)).symm.injective h
  funext j
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1 (congrFun h' j)

def tautFamily : JetFamily (vecObj X d) x0 d :=
  fun m => vecPt x0 d fun j => (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)) : Jet S (Fin 1 × Fin d) m)

end Model

end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
