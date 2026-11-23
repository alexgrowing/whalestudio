import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjTangentVectorAddAtPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.GrpTangentPt

noncomputable section

namespace GlobalTheory.TanPtMod

variable {S : Scheme.{0}} {k : Type} [CommRing k] (x : Sp k ⟶ S)

def epsZeroPt : Over.mk x ⟶ epsPtR x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = x
    rw [← Category.assoc, ← Spec.map_comp]
    conv_rhs => rw [← Category.id_comp x]
    congr 1
    rw [← Spec.map_id]
    congr 1)

@[simp] lemma epsZeroPt_left : (epsZeroPt x).left = spMap (TrivSqZeroExt.fstHom k k k).toRingHom := rfl

@[reassoc]
lemma epsZeroPt_epsScalePt (c : k) : epsZeroPt x ≫ epsScalePt x c = epsZeroPt x := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  simp

lemma epsScalePt_mul (a b : k) : epsScalePt x a ≫ epsScalePt x b = epsScalePt x (a * b) := by
  rw [sqZeroMapPt_comp]
  congr 1
  refine LinearMap.ext_ring ?_
  simp [mul_comm]

variable (G : Over S) [GrpObj G] [IsCommMonObj G]

def tanSub : Subgroup (epsPtR x ⟶ G) where
  carrier := {w | epsZeroPt x ≫ w = 1}
  one_mem' := comp_one _
  mul_mem' {a b} ha hb := by
    change epsZeroPt x ≫ (a * b) = 1
    rw [comp_mul, ha, hb, _root_.one_mul]
  inv_mem' {a} ha := by
    change epsZeroPt x ≫ a⁻¹ = 1
    rw [GrpObj.comp_inv, ha, _root_.inv_one]

lemma mem_tanSub_iff (w : epsPtR x ⟶ G) :
    w ∈ tanSub x G ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left := by
  change epsZeroPt x ≫ w = 1 ↔ _
  exact ⟨fun h => congrArg Over.Hom.left h, fun h => Over.OverMorphism.ext h⟩

abbrev Tan : Type := Additive (tanSub x G)

variable {x G}

def Tan.hom (v : Tan x G) : epsPtR x ⟶ G := (Additive.toMul v : tanSub x G).1

def Tan.mk (w : epsPtR x ⟶ G) (hw : w ∈ tanSub x G) : Tan x G := Additive.ofMul ⟨w, hw⟩

@[simp] lemma Tan.hom_mk (w : epsPtR x ⟶ G) (hw : w ∈ tanSub x G) : (Tan.mk w hw).hom = w := rfl

lemma Tan.hom_mem (v : Tan x G) : v.hom ∈ tanSub x G := (Additive.toMul v : tanSub x G).2

@[ext] lemma Tan.ext {v w : Tan x G} (h : v.hom = w.hom) : v = w :=
  Additive.toMul.injective (Subtype.ext h)

@[simp] lemma Tan.hom_zero : (0 : Tan x G).hom = 1 := rfl
@[simp] lemma Tan.hom_add (v w : Tan x G) : (v + w).hom = v.hom * w.hom := rfl

def Tan.homAdd : Tan x G →+ Additive (epsPtR x ⟶ G) := (tanSub x G).subtype.toAdditive

lemma Tan.hom_sum {I : Type} (s : Finset I) (v : I → Tan x G) : (∑ i ∈ s, v i).hom = ∏ i ∈ s, (v i).hom := by
  have := map_sum (Tan.homAdd (x := x) (G := G)) v s
  exact congrArg Additive.toMul this

instance : Module k (Tan x G) where
  smul c v := Tan.mk (epsScalePt x c ≫ v.hom) (by
    change epsZeroPt x ≫ _ = 1
    rw [epsZeroPt_epsScalePt_assoc]; exact v.hom_mem)
  one_smul v := Tan.ext (by
    change epsScalePt x 1 ≫ v.hom = _
    rw [epsScalePt_one, Category.id_comp])
  mul_smul a b v := Tan.ext (by
    change epsScalePt x (a * b) ≫ v.hom = epsScalePt x a ≫ epsScalePt x b ≫ v.hom
    rw [← Category.assoc, epsScalePt_mul])
  smul_zero c := Tan.ext (comp_one _)
  smul_add c v w := Tan.ext (comp_mul _ _ _)
  add_smul a b v := Tan.ext (epsScalePt_add_comp x a b ((mem_tanSub_iff x G _).mp v.hom_mem))
  zero_smul v := Tan.ext (epsScalePt_zero_comp x ((mem_tanSub_iff x G _).mp v.hom_mem))

@[simp] lemma Tan.hom_smul (c : k) (v : Tan x G) : (c • v).hom = epsScalePt x c ≫ v.hom := rfl

def Tan.map (f : G ⟶ G) [IsMonHom f] : Tan x G →ₗ[k] Tan x G where
  toFun v := Tan.mk (v.hom ≫ f) (by
    change epsZeroPt x ≫ _ = 1
    rw [← Category.assoc, v.hom_mem, one_comp])
  map_add' v w := Tan.ext (mul_comp _ _ _)
  map_smul' c v := Tan.ext (Category.assoc _ _ _)

@[simp] lemma Tan.hom_map (f : G ⟶ G) [IsMonHom f] (v : Tan x G) : (Tan.map f v).hom = v.hom ≫ f := rfl

def actEnd {O : Type} [Ring O] (a : OActN O G) : O →+* Module.End k (Tan x G) where
  toFun b := haveI := a.hom b; Tan.map (a.act b)
  map_one' := by
    ext v
    simp [a.one]
  map_mul' b c := by
    ext v
    simp [a.mul, Module.End.mul_apply]
  map_zero' := by
    have h : a.act 0 = 1 := by
      have := a.add 0 0
      rw [add_zero] at this
      exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
    refine LinearMap.ext fun v => Tan.ext ?_
    change v.hom ≫ a.act 0 = 1
    rw [h, comp_one]
  map_add' b c := by
    ext v
    simp [a.add, comp_mul]

@[simp] lemma actEnd_hom {O : Type} [Ring O] (a : OActN O G) (b : O) (v : Tan x G) :
    (actEnd a b v).hom = v.hom ≫ a.act b := rfl

end GlobalTheory.TanPtMod
