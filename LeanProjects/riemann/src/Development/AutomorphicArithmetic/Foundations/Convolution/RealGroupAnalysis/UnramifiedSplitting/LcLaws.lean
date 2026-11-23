import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.lcLaws :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K), (∀ b, lc v (nL b) = gl (nU (sg v b))) ∧ (∀ a, lc v (dL a a⁻¹) = gl (mD (idl v a))) ∧ (∀ t, lc v (dL 1 t) = dM (idl v t)) ∧
      (∀ a, lc v (dL a 1) = aE (idl v a)) ∧ (∀ a, lc v (dL a a) = Matrix.GeneralLinearGroup.scalar (Fin 2) (idl v a)) ∧
      (∀ y, Matrix.GeneralLinearGroup.map (cp v) (lc v y) = y) ∧
      ∀ (g : GL (Fin 2) (A K)) y, lc v y * g = g * lc v ((Matrix.GeneralLinearGroup.map (cp v) g)⁻¹ * y * Matrix.GeneralLinearGroup.map (cp v) g) := by
  intro K _ _ v
  obtain ⟨hadd, hmul, hcp, hidl, hlc, -, -, -, -, -⟩ := sgLaws K v
  have h0 : sg v 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have hinv : ∀ a : (Kv v)ˣ, idl v a⁻¹ = (idl v a)⁻¹ := fun a => map_inv (localIdele K v) a
  have hv : ∀ a : (Kv v)ˣ, 1 + sg v ((a : Kv v) - 1) = ((idl v a : (A K)ˣ) : A K) := fun a => (hidl a).symm
  have hvi : ∀ a : (Kv v)ˣ, 1 + sg v (((a⁻¹ : (Kv v)ˣ) : Kv v) - 1) = (((idl v a)⁻¹ : (A K)ˣ) : A K) := fun a => by
    rw [← hinv, hidl]
  have hvi' : ∀ a : (Kv v)ˣ, 1 + sg v ((a : Kv v)⁻¹ - 1) = (((idl v a)⁻¹ : (A K)ˣ) : A K) := fun a => by
    rw [← hvi a, Units.val_inv_eq_inv_val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    apply Units.ext
    ext i j
    rw [hlc]
    fin_cases i <;> fin_cases j <;> simp [nL, nU, h0] <;> rfl
  · intro a
    apply Units.ext
    ext i j
    rw [hlc]
    fin_cases i <;> fin_cases j <;> simp [dL, mD, h0, hv, hvi'] <;> rfl
  · intro t
    apply Units.ext
    ext i j
    rw [hlc]
    fin_cases i <;> fin_cases j <;> simp [dL, dM, h0, hv]
  · intro a
    apply Units.ext
    ext i j
    rw [hlc]
    fin_cases i <;> fin_cases j <;> simp [dL, aE, h0, hv]
  · intro a
    apply Units.ext
    ext i j
    rw [hlc]
    fin_cases i <;> fin_cases j <;> simp [dL, h0, hv]
  · intro y
    apply Units.ext
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hlc, map_add, hcp]
    fin_cases i <;> fin_cases j <;> simp
  · intro g y
    have one_l : ∀ (R : Type) [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2),
        (1 : Matrix (Fin 2) (Fin 2) R) i 0 * M 0 j + (1 : Matrix (Fin 2) (Fin 2) R) i 1 * M 1 j = M i j := fun R _ M i j => by
      have := congrFun (congrFun (Matrix.one_mul M) i) j
      rwa [Matrix.mul_apply, Fin.sum_univ_two] at this
    have one_r : ∀ (R : Type) [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2),
        M i 0 * (1 : Matrix (Fin 2) (Fin 2) R) 0 j + M i 1 * (1 : Matrix (Fin 2) (Fin 2) R) 1 j = M i j := fun R _ M i j => by
      have := congrFun (congrFun (Matrix.mul_one M) i) j
      rwa [Matrix.mul_apply, Fin.sum_univ_two] at this
    have hr : ∀ (x : Kv v) (a : A K), sg v x * a = sg v (x * cp v a) := fun x a => by
      rw [mul_comm, hmul, mul_comm]
    set gv := Matrix.GeneralLinearGroup.map (cp v) g with hgv
    have hgva : ∀ i j, gv.val i j = cp v (g.val i j) := fun i j => by
      rw [hgv, Matrix.GeneralLinearGroup.map_apply]
    generalize hzd : gv⁻¹ * y * gv = z
    have hz : gv * z = y * gv := by
      rw [← hzd]; group
    apply Units.ext
    ext i j
    have hz' : gv.val i 0 * z.val 0 j + gv.val i 1 * z.val 1 j = y.val i 0 * gv.val 0 j + y.val i 1 * gv.val 1 j := by
      have := congrArg (fun h : GL (Fin 2) (Kv v) => h.val i j) hz
      simpa only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] using this
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hlc]
    simp only [add_mul, mul_add, hr, hmul, ← hgva]
    have e : (y.val i 0 - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i 0) * gv.val 0 j + (y.val i 1 - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i 1) * gv.val 1 j
        = gv.val i 0 * (z.val 0 j - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) 0 j) + gv.val i 1 * (z.val 1 j - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) 1 j) := by
      linear_combination -hz' - one_l (Kv v) gv.val i j + one_r (Kv v) gv.val i j
    have es := congrArg (sg v) e
    rw [hadd, hadd] at es
    linear_combination es + one_l (A K) g.val i j - one_r (A K) g.val i j
