import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Tan

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (G : Over X0) [GrpObj G] [IsCommMonObj G]

def tanSub : Subgroup (overAt x0 (DualNumber S) ⟶ G) := (smHom (G := G) x0 0).ker

theorem mem_tanSub {v : overAt x0 (DualNumber S) ⟶ G} : v ∈ tanSub x0 G ↔ smT x0 0 v = 1 := MonoidHom.mem_ker

abbrev TanM : Type := Additive (tanSub x0 G)

variable {x0 G}

def tv (v : TanM x0 G) : overAt x0 (DualNumber S) ⟶ G := ((Additive.toMul v : tanSub x0 G) : overAt x0 (DualNumber S) ⟶ G)

theorem tv_mem (v : TanM x0 G) : smT x0 0 (tv v) = 1 := (mem_tanSub x0 G).1 (Additive.toMul v).2

theorem tanM_ext {u v : TanM x0 G} (h : tv u = tv v) : u = v := Additive.toMul.injective (Subtype.ext h)

theorem tv_add (u v : TanM x0 G) : tv (u + v) = tv u * tv v := rfl
theorem tv_zero : tv (0 : TanM x0 G) = 1 := rfl

def mkT (v : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 v = 1) : TanM x0 G := Additive.ofMul ⟨v, (mem_tanSub x0 G).2 h⟩

theorem tv_mkT (v : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 v = 1) : tv (mkT v h) = v := rfl

theorem smT_mem (a : S) (v : TanM x0 G) : smT x0 0 (smT x0 a (tv v)) = 1 := by
  rw [smT_smT, zero_mul, tv_mem]

instance : SMul S (TanM x0 G) := ⟨fun a v => mkT (smT x0 a (tv v)) (smT_mem a v)⟩

theorem tv_smul (a : S) (v : TanM x0 G) : tv (a • v) = smT x0 a (tv v) := rfl

instance : Module S (TanM x0 G) where
  one_smul v := tanM_ext (smT_unit x0 _)
  mul_smul a b v := tanM_ext (smT_smT x0 a b (tv v)).symm
  smul_zero a := tanM_ext (smT_one' x0 a)
  smul_add a u v := tanM_ext (smT_mul x0 a (tv u) (tv v))
  add_smul a b v := tanM_ext (smT_add x0 (tv v) (tv_mem v) a b)
  zero_smul v := tanM_ext (tv_mem v)

def actL (φ : G ⟶ G) [IsMonHom φ] : TanM x0 G →ₗ[S] TanM x0 G where
  toFun v := mkT (tv v ≫ φ) (by rw [smT_post, tv_mem, MonObj.one_comp])
  map_add' u v := tanM_ext (MonObj.mul_comp (tv u) (tv v) φ)
  map_smul' a v := tanM_ext (smT_post x0 a (tv v) φ).symm

theorem tv_actL (φ : G ⟶ G) [IsMonHom φ] (v : TanM x0 G) : tv (actL φ v) = tv v ≫ φ := rfl

theorem oact_zero {O : Type} [CommRing O] (A : OAct O G) : A.act 0 = 1 := by
  have h := A.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

def actR {O : Type} [CommRing O] (A : OAct O G) : O →+* Module.End S (TanM x0 G) where
  toFun a := @actL _ _ _ x0 G _ _ (A.act a) (A.hom a)
  map_one' := LinearMap.ext fun v => tanM_ext (by
    show tv v ≫ A.act 1 = tv v
    rw [A.one, Category.comp_id])
  map_mul' a b := LinearMap.ext fun v => tanM_ext (by
    show tv v ≫ A.act (a * b) = (tv v ≫ A.act b) ≫ A.act a
    rw [mul_comm a b, A.mul, Category.assoc])
  map_zero' := LinearMap.ext fun v => tanM_ext (by
    show tv v ≫ A.act 0 = 1
    rw [oact_zero A, MonObj.comp_one])
  map_add' a b := LinearMap.ext fun v => tanM_ext (by
    show tv v ≫ A.act (a + b) = (tv v ≫ A.act a) * (tv v ≫ A.act b)
    rw [A.add, MonObj.comp_mul])

theorem tv_actR {O : Type} [CommRing O] (A : OAct O G) (a : O) (v : TanM x0 G) :
    tv (actR A a v) = tv v ≫ A.act a := rfl

end Tan

end ReciprocityTheory.ChartRestriction.G.PullbackSections
