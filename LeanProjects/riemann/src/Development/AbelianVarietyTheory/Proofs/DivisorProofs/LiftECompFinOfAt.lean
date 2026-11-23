import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocCoLocDarboux

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem singleFin_mul (v : Pl F) (a b : Fv F v) :
    GlobalTheory.AdelicU.singleFin v (a * b) = GlobalTheory.AdelicU.singleFin v a * GlobalTheory.AdelicU.singleFin v b := by
  apply GlobalTheory.AdelicU.af_ext
  intro u
  rw [map_mul (evalV F u)]
  by_cases hu : u = v
  · subst hu
    rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, zero_mul]

theorem liftV_mul (v : Pl F) (a b : Fv F v) :
    GlobalTheory.LatVac.liftV v (a * b) = GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b := by
  change ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v (a * b)) =
    ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a) * ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v b)
  rw [Prod.mk_mul_mk, mul_zero, singleFin_mul]

theorem liftE_mul (v : Pl F) (x y : Fv F v ⊗[F] E) : liftE v (x * y) = liftE v x * liftE v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | tmul b f =>
      simp only [liftE, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
        liftV_mul]

theorem one_add_liftE_mul (v : Pl F) (x y : Fv F v ⊗[F] E) :
    (1 + liftE v (x - 1)) * (1 + liftE v (y - 1)) = 1 + liftE v (x * y - 1) := by
  have : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by ring
  rw [this, map_add, map_add, liftE_mul]
  ring

theorem one_add_liftV_mul (v : Pl F) (x y : Fv F v) :
    (1 + GlobalTheory.LatVac.liftV v (x - 1)) * (1 + GlobalTheory.LatVac.liftV v (y - 1)) = 1 + GlobalTheory.LatVac.liftV v (x * y - 1) := by
  have : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by ring
  rw [this, map_add, map_add, liftV_mul]
  ring

def liftU (v : Pl F) : (Fv F v ⊗[F] E)ˣ →* (AE F E)ˣ where
  toFun z := ⟨1 + liftE v ((z : Fv F v ⊗[F] E) - 1), 1 + liftE v (((z⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) - 1),
    by rw [one_add_liftE_mul, Units.mul_inv, sub_self, map_zero, add_zero],
    by rw [one_add_liftE_mul, Units.inv_mul, sub_self, map_zero, add_zero]⟩
  map_one' := by ext; simp
  map_mul' z w := by ext; simp only [Units.val_mul, Units.val_mk]; rw [one_add_liftE_mul]

def liftUF (v : Pl F) : (Fv F v)ˣ →* (AF F)ˣ where
  toFun a := ⟨1 + GlobalTheory.LatVac.liftV v ((a : Fv F v) - 1), 1 + GlobalTheory.LatVac.liftV v (((a⁻¹ : (Fv F v)ˣ) : Fv F v) - 1),
    by rw [one_add_liftV_mul, Units.mul_inv, sub_self, map_zero, add_zero],
    by rw [one_add_liftV_mul, Units.inv_mul, sub_self, map_zero, add_zero]⟩
  map_one' := by ext; simp
  map_mul' z w := by ext; simp only [Units.val_mul, Units.val_mk]; rw [one_add_liftV_mul]

theorem liftU_val (v : Pl F) (z : (Fv F v ⊗[F] E)ˣ) :
    ((liftU v z : (AE F E)ˣ) : AE F E) = 1 + liftE v ((z : Fv F v ⊗[F] E) - 1) := rfl

theorem liftUF_val (v : Pl F) (a : (Fv F v)ˣ) :
    ((liftUF v a : (AF F)ˣ) : AF F) = 1 + GlobalTheory.LatVac.liftV v ((a : Fv F v) - 1) := rfl

def locChr (χ : Chr F E) (v : Pl F) : (Fv F v ⊗[F] E)ˣ →* Circle := χ.comp (liftU v)

end GlobalTheory.HoweLocal

namespace GlobalTheory.HoweLocal

theorem norm_map_tensor {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) (x : A ⊗[F] E) :
    Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id F E) x) = f (Algebra.norm A x) := by
  classical
  let b := Module.finBasis F E
  let bA := Algebra.TensorProduct.basis A b
  let bB := Algebra.TensorProduct.basis B b
  have hrep : ∀ (y : A ⊗[F] E) i, bB.repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) i = f (bA.repr y i) := by
    intro y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp [map_add, hy, hy']
    | tmul a e =>
      simp [bA, bB, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  have hb : ∀ j, bB j = Algebra.TensorProduct.map f (AlgHom.id F E) (bA j) := by
    intro j; simp [bA, bB, Algebra.TensorProduct.basis_apply]
  rw [Algebra.norm_eq_matrix_det bB, Algebra.norm_eq_matrix_det bA]
  show _ = (f : A →+* B) _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_eq_repr_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [hb, ← map_mul, hrep]
  rfl

end GlobalTheory.HoweLocal

namespace GlobalTheory.HoweLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftU_algebraMap (v : Pl F) (a : (Fv F v)ˣ) :
    liftU (E := E) v (Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E) : Fv F v →* Fv F v ⊗[F] E) a) =
      Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (liftUF v a) := by
  ext
  rw [liftU_val, Units.coe_map, Units.coe_map, liftUF_val, MonoidHom.coe_coe, MonoidHom.coe_coe, map_add, map_one]
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.one_def,
    Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_self, RingHom.id_apply, ← TensorProduct.sub_tmul]
  simp only [liftE, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

end GlobalTheory.HoweLocal

namespace GlobalTheory.HoweLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftE_compFin_of_at (v : Pl F) {z : AE F E} (hz : At (evFin F v) z) : liftE v (compFin F E v z) = z := by
  rw [← GlobalTheory.HoweLocal.LocCoords.liftV_one_smul]
  have h : (1 - GlobalTheory.LatVac.liftV v 1) • z = 0 := hz _ (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

theorem liftU_compFin_of_at (v : Pl F) (a : (AE F E)ˣ) (ha : At (evFin F v) ((a : AE F E) - 1)) :
    liftU v (Units.map (compFin F E v : AE F E →* Fv F v ⊗[F] E) a) = a := by
  ext
  rw [liftU_val, Units.coe_map, MonoidHom.coe_coe, ← map_one (compFin F E v), ← map_sub, liftE_compFin_of_at v ha,
    add_sub_cancel]

end GlobalTheory.HoweLocal
