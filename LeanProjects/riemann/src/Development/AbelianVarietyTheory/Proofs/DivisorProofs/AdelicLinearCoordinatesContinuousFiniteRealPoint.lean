import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousKeepParts
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section
namespace GlobalTheory.AdelicCoordF

open GlobalTheory.AdelicCoord (incF incI incF_sndA incI_fstA pairA_mul_eq_zero_iff_snd pairA_mul_eq_zero_iff_fst)

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def secF : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incF F) LinearMap.id

def secI : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incI F) LinearMap.id

theorem secF_finPart (z : AF F ⊗[F] E) :
    secF F E (Formalism.IndefR.DatumF.finPartF F E z) = pairA F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul a b =>
    have h1 : Formalism.IndefR.DatumF.finPartF F E (a ⊗ₜ b) = sndA F a ⊗ₜ b := rfl
    rw [h1, secF, TensorProduct.map_tmul, LinearMap.id_apply, incF_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem secI_infPart (z : AF F ⊗[F] E) :
    secI F E (Formalism.IndefR.DatumF.infPartF F E z) = pairA F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul a b =>
    have h1 : Formalism.IndefR.DatumF.infPartF F E (a ⊗ₜ b) = fstA F a ⊗ₜ b := rfl
    rw [h1, secI, TensorProduct.map_tmul, LinearMap.id_apply, incI_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem finPartF_smul (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.finPartF F E (pairA F 0 1 • z) = Formalism.IndefR.DatumF.finPartF F E z := by
  rw [Algebra.smul_def, map_mul]
  have : Formalism.IndefR.DatumF.finPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA F (algebraMap (AF F) (AF F) (pairA F 0 1)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.AdelicCoord.sndA_pairA]
    rfl
  rw [this, one_mul]

theorem infPartF_smul (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.infPartF F E (pairA F 1 0 • z) = Formalism.IndefR.DatumF.infPartF F E z := by
  rw [Algebra.smul_def, map_mul]
  have : Formalism.IndefR.DatumF.infPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA F (algebraMap (AF F) (AF F) (pairA F 1 0)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.AdelicCoord.fstA_pairA]
    rfl
  rw [this, one_mul]

theorem finPartF_eq_zero_iff (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.finPartF F E z = 0 ↔ pairA F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secF_finPart, h, map_zero]
  · intro h; rw [← finPartF_smul, h, map_zero]

theorem infPartF_eq_zero_iff (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.infPartF F E z = 0 ↔ pairA F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secI_infPart, h, map_zero]
  · intro h; rw [← infPartF_smul, h, map_zero]

theorem smul_vec_fin {N : ℕ} (u : Fin N → AF F) : pairA F 0 1 • u = 0 ↔ GlobalTheory.SWQ.fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd F (u l)

theorem smul_vec_inf {N : ℕ} (u : Fin N → AF F) : pairA F 1 0 • u = 0 ↔ GlobalTheory.SWQ.inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst F (u l)

theorem smul_pair_eq_zero {N : ℕ} (c : AF F) (w : GlobalTheory.ThetaTransform.VA F N) :
    c • w = 0 ↔ c • w.1 = 0 ∧ c • w.2 = 0 :=
  Prod.ext_iff

theorem coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    Continuous e ∧ Continuous e.symm ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.finPartF F E) = 0 ↔
        GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.infPartF F E) = 0 ↔
        GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  intro F E _ _ _ _ _ nS nT N e
  haveI h0 : IsModuleTopology (AF F) (AF F ⊗[F] E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI hA : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI h1 : IsModuleTopology (AF F) (Fin nS → AF F ⊗[F] E) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (Formalism.IndefR.DatumF.finPartF F E) = 0 ↔ pairA F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPartF_eq_zero_iff F E (x i j)
    rw [key, ← smul_vec_fin, ← smul_vec_fin, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]
  · have key : x.map (Formalism.IndefR.DatumF.infPartF F E) = 0 ↔ pairA F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPartF_eq_zero_iff F E (x i j)
    rw [key, ← smul_vec_inf, ← smul_vec_inf, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]

end GlobalTheory.AdelicCoordF

end
