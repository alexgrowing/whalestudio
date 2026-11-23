import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ

section Ad

variable (F : Type) [Field F] [NumberField F]

theorem fstA_pairA' (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA' (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

variable {F} in
theorem af_ext' {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

theorem pairA_mul_eq_zero_iff_snd' (a : AF F) : pairA F 0 1 * a = 0 ↔ sndA F a = 0 := by
  constructor
  · intro h
    have := congrArg (sndA F) h
    rwa [map_mul, map_zero, sndA_pairA', one_mul] at this
  · intro h
    refine af_ext' ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA', zero_mul]
    · rw [map_mul, map_zero, sndA_pairA', h, mul_zero]

theorem pairA_mul_eq_zero_iff_fst' (a : AF F) : pairA F 1 0 * a = 0 ↔ fstA F a = 0 := by
  constructor
  · intro h
    have := congrArg (fstA F) h
    rwa [map_mul, map_zero, fstA_pairA', one_mul] at this
  · intro h
    refine af_ext' ?_ ?_
    · rw [map_mul, map_zero, fstA_pairA', h, mul_zero]
    · rw [map_mul, map_zero, sndA_pairA', zero_mul]

def incFin : Af F →ₗ[F] AF F where
  toFun y := pairA F 0 y
  map_add' y y' := af_ext' (by rw [map_add, fstA_pairA', fstA_pairA', fstA_pairA', add_zero])
    (by rw [map_add, sndA_pairA', sndA_pairA', sndA_pairA'])
  map_smul' c y := af_ext' (by rw [map_smul, fstA_pairA', fstA_pairA', RingHom.id_apply, smul_zero])
    (by rw [map_smul, sndA_pairA', sndA_pairA', RingHom.id_apply])

def incInf : Ainf F →ₗ[F] AF F where
  toFun y := pairA F y 0
  map_add' y y' := af_ext' (by rw [map_add, fstA_pairA', fstA_pairA', fstA_pairA'])
    (by rw [map_add, sndA_pairA', sndA_pairA', sndA_pairA', add_zero])
  map_smul' c y := af_ext' (by rw [map_smul, fstA_pairA', fstA_pairA', RingHom.id_apply])
    (by rw [map_smul, sndA_pairA', sndA_pairA', RingHom.id_apply, smul_zero])

theorem incFin_sndA (a : AF F) : incFin F (sndA F a) = pairA F 0 1 * a :=
  af_ext' (by rw [map_mul, fstA_pairA', zero_mul]; rfl) (by rw [map_mul, sndA_pairA', one_mul]; rfl)

theorem incInf_fstA (a : AF F) : incInf F (fstA F a) = pairA F 1 0 * a :=
  af_ext' (by rw [map_mul, fstA_pairA', one_mul]; rfl) (by rw [map_mul, sndA_pairA', zero_mul]; rfl)

end Ad

section Coord

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def secFin : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incFin F) LinearMap.id

def secInf : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incInf F) LinearMap.id

variable {F E}

theorem secFin_finPartF (z : AF F ⊗[F] E) : secFin F E (finPartF F E z) = pairA F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(finPartF F E).map_zero, (secFin F E).map_zero, smul_zero]
  | tmul a b =>
    have h1 : finPartF F E (a ⊗ₜ b) = sndA F a ⊗ₜ b := rfl
    rw [h1, secFin, TensorProduct.map_tmul, LinearMap.id_apply, incFin_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [(finPartF F E).map_add, (secFin F E).map_add, hx, hy, smul_add]

theorem secInf_infPartF (z : AF F ⊗[F] E) : secInf F E (infPartF F E z) = pairA F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(infPartF F E).map_zero, (secInf F E).map_zero, smul_zero]
  | tmul a b =>
    have h1 : infPartF F E (a ⊗ₜ b) = fstA F a ⊗ₜ b := rfl
    rw [h1, secInf, TensorProduct.map_tmul, LinearMap.id_apply, incInf_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [(infPartF F E).map_add, (secInf F E).map_add, hx, hy, smul_add]

theorem finPartF_smul (z : AF F ⊗[F] E) : finPartF F E (pairA F 0 1 • z) = finPartF F E z := by
  rw [Algebra.smul_def, (finPartF F E).map_mul]
  have : finPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA F (algebraMap (AF F) (AF F) (pairA F 0 1)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, sndA_pairA']
    rfl
  rw [this, one_mul]

theorem infPartF_smul (z : AF F ⊗[F] E) : infPartF F E (pairA F 1 0 • z) = infPartF F E z := by
  rw [Algebra.smul_def, (infPartF F E).map_mul]
  have : infPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA F (algebraMap (AF F) (AF F) (pairA F 1 0)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, fstA_pairA']
    rfl
  rw [this, one_mul]

theorem finPartF_eq_zero_iff (z : AF F ⊗[F] E) : finPartF F E z = 0 ↔ pairA F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secFin_finPartF, h, (secFin F E).map_zero]
  · intro h; rw [← finPartF_smul, h, (finPartF F E).map_zero]

theorem infPartF_eq_zero_iff (z : AF F ⊗[F] E) : infPartF F E z = 0 ↔ pairA F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secInf_infPartF, h, (secInf F E).map_zero]
  · intro h; rw [← infPartF_smul, h, (infPartF F E).map_zero]

omit [Field E] [NumberField E] [Algebra F E] in
theorem smul_vec_fin' {N : ℕ} (u : Fin N → AF F) : pairA F 0 1 • u = 0 ↔ fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd' F (u l)

omit [Field E] [NumberField E] [Algebra F E] in
theorem smul_vec_inf' {N : ℕ} (u : Fin N → AF F) : pairA F 1 0 • u = 0 ↔ inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst' F (u l)

theorem coordF (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) ≃ₗ[AF F] VA F N) :
    Continuous e ∧ Continuous e.symm ∧
      (∀ x, x.map (finPartF F E) = 0 ↔ fin (e x).1 = 0 ∧ fin (e x).2 = 0) ∧
      (∀ x, x.map (infPartF F E) = 0 ↔ inf (e x).1 = 0 ∧ inf (e x).2 = 0) := by
  haveI h0 : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI h1 : IsModuleTopology (AF F) (Fin n → AF F ⊗[F] E) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF F) (Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (finPartF F E) = 0 ↔ pairA F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPartF_eq_zero_iff (x i j)
    rw [key, ← smul_vec_fin', ← smul_vec_fin', ← LinearEquiv.map_eq_zero_iff e, LinearEquiv.map_smul]
    exact Prod.ext_iff
  · have key : x.map (infPartF F E) = 0 ↔ pairA F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPartF_eq_zero_iff (x i j)
    rw [key, ← smul_vec_inf', ← smul_vec_inf', ← LinearEquiv.map_eq_zero_iff e, LinearEquiv.map_smul]
    exact Prod.ext_iff

end Coord

end GlobalTheory.ThetaTransformF

end
