import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.LatStab

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem gen_mul_transpose {n d : ℕ} (x : Fin n → E) (y : Fin d → E) (a : AF F)
    (K : Matrix (Fin d) (Fin d) (AE F E)) :
    (a • incM F (Matrix.vecMulVec x y)) * Kᵀ =
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i))
        (a • (K *ᵥ fun i => inclR (F := F) (AF F) (y i))) := by
  ext i j
  simp only [incM, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply,
    Matrix.transpose_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, map_mul, Finset.smul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  ring

theorem vecMulVec_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : Fin n → E) (hx : x ∈ X.L) (u : Fin d → AE F E)
    (hu : u ∈ AddSubgroup.closure {z | ∃ b : AF F, At (evFin F w) b ∧
          evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => inclR (F := F) (AF F) (y' i)}) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u ∈ latAtV X W w := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨b, hb, hbi, y', hy', rfl⟩ := hu
    apply AddSubgroup.subset_closure
    refine ⟨b, hb, hbi, x, hx, y', hy', ?_⟩
    ext i j
    simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, map_mul]
    rw [mul_smul_comm]
  | zero =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (0 : Fin d → AE F E) = 0 := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [this]; exact zero_mem _
  | add u v _ _ hu hv =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (u + v) =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u +
          Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) v := by
      ext i j; simp [Matrix.vecMulVec_apply, mul_add]
    rw [this]; exact add_mem hu hv
  | neg u _ hu =>
    have : Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (-u) =
        -Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) u := by
      ext i j; simp [Matrix.vecMulVec_apply]
    rw [this]; exact neg_mem hu

theorem mul_transpose_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (K : Matrix (Fin d) (Fin d) (AE F E))
    (hK : ∀ a : AF F, At (evFin F w) a → evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, At (evFin F w) b ∧
          evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => inclR (F := F) (AF F) (y' i)})
    (γ : Matrix (Fin n) (Fin d) (AE F E)) (hγ : γ ∈ latAtV X W w) : γ * Kᵀ ∈ latAtV X W w := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    rw [gen_mul_transpose]
    exact vecMulVec_mem X W w x hx _ (hK a ha hai y hy)
  | zero => simp
  | add u v _ _ hu hv => rw [Matrix.add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [Matrix.neg_mul]; exact neg_mem hu

theorem latAtV_mul_transpose_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (K K' : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), K' * K = 1 →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    (∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a → GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F →
      ∀ y ∈ W.L, a • (K' *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ W.L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)}) →
    ∀ γ, γ * Kᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w := by
  intro F E _ _ _ _ _ n d X W w K K' hKK hK hK' γ
  constructor
  · intro h
    have h2 := mul_transpose_mem X W w K' hK' _ h
    rwa [Matrix.mul_assoc, ← Matrix.transpose_mul, hKK, Matrix.transpose_one, Matrix.mul_one] at h2
  · exact mul_transpose_mem X W w K hK γ

end GlobalTheory.LatStab
