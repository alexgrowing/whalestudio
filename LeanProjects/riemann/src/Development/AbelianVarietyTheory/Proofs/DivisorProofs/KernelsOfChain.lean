import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

namespace KerGrp

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

def sub (T : Over S) : Subgroup (T ⟶ A) := (IsMonHom.monoidHom f T).ker

theorem mem_sub {T : Over S} (x : T ⟶ A) : x ∈ sub f T ↔ x ≫ f = 1 := by
  simp [sub, MonoidHom.mem_ker]

def pts : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (sub f T.unop)
  map {T T'} g := GrpCat.ofHom
    { toFun := fun x => ⟨g.unop ≫ x.1, (mem_sub f _).2 (by
        rw [Category.assoc, (mem_sub f _).1 x.2, MonObj.comp_one])⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := by ext x; exact Category.id_comp _
  map_comp g h := by ext x; exact Category.assoc _ _ _

theorem fst_comp : pullback.fst f η[B] ≫ f = 1 := by
  rw [pullback.condition, Hom.one_def, toUnit_unique (pullback.snd f η[B]) (toUnit _)]

def lift {T : Over S} (x : T ⟶ A) (hx : x ≫ f = 1) : T ⟶ ker f :=
  pullback.lift x (toUnit T) (by rw [hx, Hom.one_def])

@[simp] theorem lift_fst {T : Over S} (x : T ⟶ A) (hx : x ≫ f = 1) : lift f x hx ≫ pullback.fst f η[B] = x :=
  pullback.lift_fst _ _ _

theorem hom_ext {T : Over S} {y z : T ⟶ ker f} (h : y ≫ pullback.fst f η[B] = z ≫ pullback.fst f η[B]) :
    y = z :=
  pullback.hom_ext h (toUnit_unique _ _)

def rep : (pts f ⋙ forget _).RepresentableBy (ker f) where
  homEquiv {T} :=
    { toFun := fun y => (⟨y ≫ pullback.fst f η[B], (mem_sub f _).2 (by rw [Category.assoc, fst_comp,
        MonObj.comp_one])⟩ : sub f T)
      invFun := fun x => lift f (x : sub f T).1 ((mem_sub f _).1 (x : sub f T).2)
      left_inv := fun y => hom_ext f (lift_fst _ _ _)
      right_inv := fun x => Subtype.ext (lift_fst _ _ _) }
  homEquiv_comp g y := Subtype.ext (Category.assoc _ _ _)

@[instance_reducible]
def grp : GrpObj (ker f) := GrpObj.ofRepresentableBy _ (pts f) (rep f)

theorem mul_fst {T : Over S} (y z : T ⟶ ker f) :
    letI := grp f
    (y * z) ≫ pullback.fst f η[B] = (y ≫ pullback.fst f η[B]) * (z ≫ pullback.fst f η[B]) := by
  letI := grp f
  have := ((yonedaGrpObjIsoOfRepresentableBy (ker f) _ (rep f)).hom.app (.op T)).hom.map_mul y z
  exact congrArg Subtype.val this

theorem isMonHom_fst : letI := grp f; IsMonHom (pullback.fst f η[B]) := by
  letI := grp f
  exact isMonHom_of_mul _ fun T y z => mul_fst f y z

instance mono_fst : Mono (pullback.fst f η[B]) := ⟨fun _ _ h => hom_ext f h⟩

end KerGrp

end GlobalTheory.IwLevel
