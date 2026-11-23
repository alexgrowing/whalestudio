import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct GlobalTheory.VacAny
open Matrix

noncomputable section
namespace GlobalTheory.VanishLocCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_mul (v : Pl F) (a b : Fv F v) :
    GlobalTheory.LatVac.liftV v (a * b) = GlobalTheory.LatVac.liftV v a * GlobalTheory.LatVac.liftV v b :=
  Prod.ext (mul_zero _).symm (GlobalTheory.AdelicU.singleFin_mul v a b)

theorem liftT_smul (v : Pl F) (a : Fv F v) (t : Fv F v ⊗[F] E) :
    GlobalTheory.VanishLoc.liftT (E := E) v (a • t) = GlobalTheory.LatVac.liftV v a • GlobalTheory.VanishLoc.liftT v t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b e =>
    rw [TensorProduct.smul_tmul', GlobalTheory.VanishLoc.liftT, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, liftV_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable {n n₁ d d₁ : ℕ}

theorem uAt_add (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (s t : Fv F v ⊗[F] E) :
    GlobalTheory.VanishLoc.uAt H H' v (s + t) = GlobalTheory.VanishLoc.uAt H H' v s + GlobalTheory.VanishLoc.uAt H H' v t := by
  simp only [GlobalTheory.VanishLoc.uAt, map_add, add_smul, Matrix.vecMulVec_add]

theorem uAt_smul (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (a : Fv F v) (t : Fv F v ⊗[F] E) :
    GlobalTheory.VanishLoc.uAt H H' v (a • t) = GlobalTheory.LatVac.liftV v a • GlobalTheory.VanishLoc.uAt H H' v t := by
  ext i j
  simp only [GlobalTheory.VanishLoc.uAt, liftT_smul, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_assoc,
    mul_smul_comm]

variable {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d}

theorem locCo_smul (M : Model σ X W) (v : Pl F) (a : Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.LatVac.locCo M.co v (GlobalTheory.LatVac.liftV v a • u) = a • GlobalTheory.LatVac.locCo M.co v u := by
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.LatVac.evFin_liftV]
  rfl

def locUAt (M : Model σ X W) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) :
    (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) where
  toFun t := GlobalTheory.LatVac.locCo M.co v (GlobalTheory.VanishLoc.uAt H H' v t)
  map_add' s t := by rw [uAt_add, map_add]
  map_smul' a t := by rw [uAt_smul, locCo_smul, RingHom.id_apply]

theorem tendsto_locCo_uAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F),
    Tendsto (fun t : Fv F v ⊗[F] E => GlobalTheory.LatVac.locCo M.co v (GlobalTheory.VanishLoc.uAt H H' v t)) (nhds 0) (nhds 0) := by
  intro F E _ _ _ _ _ σ n d n₁ d₁ X W M H H' v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (locUAt M H H' v) := IsModuleTopology.continuous_of_linearMap _
  have h := hc.tendsto 0
  rw [map_zero] at h
  exact h

end GlobalTheory.VanishLocCont
