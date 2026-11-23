import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensInclInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDeriva
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivati
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl

noncomputable section

namespace GlobalTheory.FockInclK

open Formalism.BasicNotions.TH GlobalTheory.FockIncl

section Mats

variable {R S : ℕ}

def incMat (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) : Matrix (Ix (R + 1) (S + 1)) (Ix R S) ℂ :=
  Matrix.of fun a c => if a = skipIx r₀ s₀ c then 1 else 0

def extMat (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (Y : Mat R S) : Mat (R + 1) (S + 1) :=
  incMat r₀ s₀ * Y * (incMat r₀ s₀)ᵀ

variable (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1))

theorem mul_incMat_apply {m : Type} (M : Matrix m (Ix (R + 1) (S + 1)) ℂ) (i : m) (c : Ix R S) :
    (M * incMat r₀ s₀) i c = M i (skipIx r₀ s₀ c) := by
  simp [Matrix.mul_apply, incMat]

theorem incMat_transpose_mul : (incMat r₀ s₀)ᵀ * incMat r₀ s₀ = 1 := by
  ext c d
  rw [mul_incMat_apply]
  simp [incMat, Matrix.one_apply, (skipIx_injective r₀ s₀).eq_iff, eq_comm]

theorem extMat_mul_incMat (Y : Mat R S) : extMat r₀ s₀ Y * incMat r₀ s₀ = incMat r₀ s₀ * Y := by
  rw [extMat, Matrix.mul_assoc, incMat_transpose_mul, Matrix.mul_one]

theorem trace_extMat (Y : Mat R S) : (extMat r₀ s₀ Y).trace = Y.trace := by
  rw [extMat, Matrix.trace_mul_comm, ← Matrix.mul_assoc, incMat_transpose_mul, Matrix.one_mul]

theorem sameBlock_skipIx (c d : Ix R S) : sameBlock (skipIx r₀ s₀ c) (skipIx r₀ s₀ d) ↔ sameBlock c d := by
  rcases c with c | c <;> rcases d with d | d <;> simp [skipIx, sameBlock]

theorem extMat_apply (Y : Mat R S) (a b : Ix (R + 1) (S + 1)) :
    extMat r₀ s₀ Y a b = ∑ c, ∑ d, (if a = skipIx r₀ s₀ c then 1 else 0) * Y c d * (if b = skipIx r₀ s₀ d then 1 else 0) := by
  simp only [extMat, Matrix.mul_apply, incMat, Matrix.of_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem isKC_extMat {Y : Mat R S} (hY : IsKC Y) : IsKC (extMat r₀ s₀ Y) := by
  intro a b hab
  rw [extMat_apply]
  refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
  by_cases ha : a = skipIx r₀ s₀ c
  · by_cases hb : b = skipIx r₀ s₀ d
    · subst ha hb
      rw [hY c d fun h => hab ((sameBlock_skipIx r₀ s₀ c d).2 h)]
      simp
    · simp [hb]
  · simp [ha]

theorem Jm_apply (a b : Ix R S) : Jm R S a b = if a = b then Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) a else 0 := by
  rcases a with i | i <;> rcases b with j | j <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.one_apply] <;> split_ifs <;> simp_all

theorem Jm_mul_incMat : Jm (R + 1) (S + 1) * incMat r₀ s₀ = incMat r₀ s₀ * Jm R S := by
  ext a c
  rw [mul_incMat_apply, Matrix.mul_apply]
  simp only [Jm_apply, incMat, Matrix.of_apply]
  rw [Finset.sum_eq_single c]
  · by_cases h : a = skipIx r₀ s₀ c
    · subst h; rcases c with c | c <;> simp [skipIx]
    · simp [h]
  · intro d _ hd; simp [hd]
  · simp

theorem incMat_conjTranspose : (incMat r₀ s₀)ᴴ = (incMat r₀ s₀)ᵀ := by
  ext c a
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, incMat, Matrix.of_apply]
  split_ifs <;> simp

theorem incMat_transpose_conjTranspose : ((incMat r₀ s₀)ᵀ)ᴴ = incMat r₀ s₀ := by
  ext a c
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, incMat, Matrix.of_apply]
  split_ifs <;> simp

theorem Jm_transpose (R S : ℕ) : (Jm R S)ᵀ = Jm R S := by
  ext a b
  rw [Matrix.transpose_apply, Jm_apply, Jm_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem incMat_transpose_mul_Jm : (incMat r₀ s₀)ᵀ * Jm (R + 1) (S + 1) = Jm R S * (incMat r₀ s₀)ᵀ := by
  have := congrArg Matrix.transpose (Jm_mul_incMat r₀ s₀)
  simpa [Matrix.transpose_mul, Jm_transpose] using this

theorem extMat_mem_upq {Y : Mat R S} (hY : Y ∈ upq R S) : extMat r₀ s₀ Y ∈ upq (R + 1) (S + 1) := by
  have hY' : Yᴴ * Jm R S + Jm R S * Y = 0 := hY
  show (extMat r₀ s₀ Y)ᴴ * Jm (R + 1) (S + 1) + Jm (R + 1) (S + 1) * extMat r₀ s₀ Y = 0
  have e : (extMat r₀ s₀ Y)ᴴ = incMat r₀ s₀ * Yᴴ * (incMat r₀ s₀)ᵀ := by
    rw [extMat, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, incMat_conjTranspose, incMat_transpose_conjTranspose,
      Matrix.mul_assoc]
  rw [e, extMat, Matrix.mul_assoc, Matrix.mul_assoc, incMat_transpose_mul_Jm, ← Matrix.mul_assoc (Jm _ _),
    ← Matrix.mul_assoc (Jm _ _), Jm_mul_incMat]
  calc _ = incMat r₀ s₀ * (Yᴴ * Jm R S + Jm R S * Y) * (incMat r₀ s₀)ᵀ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY']; simp

end Mats

open scoped Matrix.Norms.Operator in
set_option backward.isDefEq.respectTransparency false in

theorem exp_mul_of_mul {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} {ι : Matrix m n ℂ} (h : A * ι = ι * B) :
    NormedSpace.exp A * ι = ι * NormedSpace.exp B := by
  have hp : ∀ k : ℕ, A ^ k * ι = ι * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  let fR : Matrix m m ℂ →+ Matrix m n ℂ :=
    { toFun := fun X => X * ι, map_zero' := Matrix.zero_mul ι, map_add' := fun X Y => Matrix.add_mul X Y ι }
  let fL : Matrix n n ℂ →+ Matrix m n ℂ :=
    { toFun := fun X => ι * X, map_zero' := Matrix.mul_zero ι, map_add' := fun X Y => Matrix.mul_add ι X Y }
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).map fR (continuous_id.matrix_mul continuous_const)
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B).map fL (continuous_const.matrix_mul continuous_id)
  have e : (fR ∘ fun k : ℕ => ((k.factorial : ℂ)⁻¹) • A ^ k) = (fL ∘ fun k : ℕ => ((k.factorial : ℂ)⁻¹) • B ^ k) := by
    funext k
    simp only [Function.comp_apply, fR, fL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.smul_mul, Matrix.mul_smul, hp]
  rw [e] at h1
  exact h1.unique h2

end GlobalTheory.FockInclK
