import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicCoord

section Ad

variable (F : Type) [Field F] [NumberField F]

theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

variable {F} in
theorem af_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

theorem pairA_mul_eq_zero_iff_snd (a : AF F) : pairA F 0 1 * a = 0 ↔ sndA F a = 0 := by
  constructor
  · intro h
    have := congrArg (sndA F) h
    rwa [map_mul, map_zero, sndA_pairA, one_mul] at this
  · intro h
    refine af_ext ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA, zero_mul]
    · rw [map_mul, map_zero, sndA_pairA, h, mul_zero]

theorem pairA_mul_eq_zero_iff_fst (a : AF F) : pairA F 1 0 * a = 0 ↔ fstA F a = 0 := by
  constructor
  · intro h
    have := congrArg (fstA F) h
    rwa [map_mul, map_zero, fstA_pairA, one_mul] at this
  · intro h
    refine af_ext ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA, h, mul_zero]
    · rw [map_mul, map_zero, sndA_pairA, zero_mul]

def incF : Af F →ₗ[F] AF F where
  toFun y := pairA F 0 y
  map_add' y y' := af_ext (by rw [map_add, fstA_pairA, fstA_pairA, fstA_pairA, add_zero])
    (by rw [map_add, sndA_pairA, sndA_pairA, sndA_pairA])
  map_smul' c y := af_ext (by rw [map_smul, fstA_pairA, fstA_pairA, RingHom.id_apply, smul_zero])
    (by rw [map_smul, sndA_pairA, sndA_pairA, RingHom.id_apply])

def incI : Ainf F →ₗ[F] AF F where
  toFun y := pairA F y 0
  map_add' y y' := af_ext (by rw [map_add, fstA_pairA, fstA_pairA, fstA_pairA])
    (by rw [map_add, sndA_pairA, sndA_pairA, sndA_pairA, add_zero])
  map_smul' c y := af_ext (by rw [map_smul, fstA_pairA, fstA_pairA, RingHom.id_apply])
    (by rw [map_smul, sndA_pairA, sndA_pairA, RingHom.id_apply, smul_zero])

theorem incF_sndA (a : AF F) : incF F (sndA F a) = pairA F 0 1 * a :=
  af_ext (by rw [map_mul, fstA_pairA, zero_mul]; rfl) (by rw [map_mul, sndA_pairA, one_mul]; rfl)

theorem incI_fstA (a : AF F) : incI F (fstA F a) = pairA F 1 0 * a :=
  af_ext (by rw [map_mul, fstA_pairA, one_mul]; rfl) (by rw [map_mul, sndA_pairA, zero_mul]; rfl)

end Ad

variable (D : D7)

def secF : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (incF D.host.F) LinearMap.id

def secI : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (incI D.host.F) LinearMap.id

theorem secF_finPart (z : AE D) : secF D (finPart D z) = pairA D.host.F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(finPart D).map_zero, (secF D).map_zero, smul_zero]
  | tmul a b =>
    have h1 : finPart D (a ⊗ₜ b) = sndA D.host.F a ⊗ₜ b := rfl
    rw [h1, secF, TensorProduct.map_tmul, LinearMap.id_apply, incF_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [(finPart D).map_add, (secF D).map_add, hx, hy, smul_add]

theorem secI_infPart (z : AE D) : secI D (infPart D z) = pairA D.host.F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(infPart D).map_zero, (secI D).map_zero, smul_zero]
  | tmul a b =>
    have h1 : infPart D (a ⊗ₜ b) = fstA D.host.F a ⊗ₜ b := rfl
    rw [h1, secI, TensorProduct.map_tmul, LinearMap.id_apply, incI_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [(infPart D).map_add, (secI D).map_add, hx, hy, smul_add]

theorem finPart_smul (z : AE D) : finPart D (pairA D.host.F 0 1 • z) = finPart D z := by
  rw [Algebra.smul_def, (finPart D).map_mul]
  have : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA D.host.F (algebraMap (AF D.host.F) (AF D.host.F) (pairA D.host.F 0 1)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, sndA_pairA]
    rfl
  rw [this, one_mul]

theorem infPart_smul (z : AE D) : infPart D (pairA D.host.F 1 0 • z) = infPart D z := by
  rw [Algebra.smul_def, (infPart D).map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA D.host.F (algebraMap (AF D.host.F) (AF D.host.F) (pairA D.host.F 1 0)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, fstA_pairA]
    rfl
  rw [this, one_mul]

theorem finPart_eq_zero_iff (z : AE D) : finPart D z = 0 ↔ pairA D.host.F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secF_finPart, h, (secF D).map_zero]
  · intro h; rw [← finPart_smul, h, (finPart D).map_zero]

theorem infPart_eq_zero_iff (z : AE D) : infPart D z = 0 ↔ pairA D.host.F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secI_infPart, h, (secI D).map_zero]
  · intro h; rw [← infPart_smul, h, (infPart D).map_zero]

theorem smul_vec_fin {N : ℕ} (u : Fin N → AF D.host.F) : pairA D.host.F 0 1 • u = 0 ↔ GlobalTheory.SWQ.fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd D.host.F (u l)

theorem smul_vec_inf {N : ℕ} (u : Fin N → AF D.host.F) : pairA D.host.F 1 0 • u = 0 ↔ GlobalTheory.SWQ.inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst D.host.F (u l)

theorem smul_pair_eq_zero {N : ℕ} (c : AF D.host.F) (w : VA D.host.F N) : c • w = 0 ↔ c • w.1 = 0 ∧ c • w.2 = 0 :=
  Prod.ext_iff

theorem coord (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N) :
    Continuous e ∧ Continuous e.symm ∧
      (∀ x, x.map (finPart D) = 0 ↔ GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧
      (∀ x, x.map (infPart D) = 0 ↔ GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  haveI h0 : IsModuleTopology (AF D.host.F) (AE D) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI h1 : IsModuleTopology (AF D.host.F) (Fin n → AE D) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF D.host.F) (Matrix (Fin m) (Fin n) (AE D)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (finPart D) = 0 ↔ pairA D.host.F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPart_eq_zero_iff D (x i j)
    rw [key, ← smul_vec_fin, ← smul_vec_fin, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]
  · have key : x.map (infPart D) = 0 ↔ pairA D.host.F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPart_eq_zero_iff D (x i j)
    rw [key, ← smul_vec_inf, ← smul_vec_inf, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]

end GlobalTheory.AdelicCoord

end
