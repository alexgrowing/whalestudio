import Mathlib
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowstLemmas

open MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceSubstitution

open Formalism.GradedWeylDivisibility Formalism.L2.DIV

def substTr {r r' : ℕ} (n : ℕ) (x : Matrix (Fin r') (Fin r) ℂ) :
    MvPolynomial (Fin r × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin r' × Fin n) ℂ :=
  aeval fun v => ∑ b : Fin r', C (x b v.1) * X (b, v.2)

def substTrO {r r' : ℕ} (n : ℕ) (x : Matrix (Fin r') (Fin r) ℂ) :
    MvPolynomial (Option (Fin r × Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Option (Fin r' × Fin n)) ℂ :=
  aeval fun o => Option.elim o (X none) (fun v => ∑ b : Fin r', C (x b v.1) * X (some (b, v.2)))

theorem substTr_mem {r r' n : ℕ} (ν : Fin n → ℕ) (x : Matrix (Fin r') (Fin r) ℂ)
    {f : MvPolynomial (Fin r × Fin n) ℂ} (hf : f ∈ dualWeyl ℂ r n ν) : substTr n x f ∈ dualWeyl ℂ r' n ν := by
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  refine ⟨isWH_algHom (substTr n x) (colW r n) (colW r' n) (fun v => ?_) hf.1, ?_⟩
  · rw [substTr, aeval_X]
    exact IsWeightedHomogeneous.sum _ _ _ fun b _ => (isWeightedHomogeneous_X ℂ _ (b, v.2)).C_mul _
  · intro l j hlj
    have h1 : (colAddGen ℂ l j).comp (substTr n x) = (substTrO n x).comp (colAddGen ℂ l j) := by
      apply MvPolynomial.algHom_ext
      intro v
      by_cases h : v.2 = j
      · simp [substTr, colAddGen, substTrO, h, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
      · simp [substTr, colAddGen, substTrO, h]
    have h2 : (rename (R := ℂ) (some : Fin r' × Fin n → Option (Fin r' × Fin n))).comp (substTr n x) =
        (substTrO n x).comp (rename some) := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [substTr, substTrO]
    have e1 := DFunLike.congr_fun h1 f
    have e2 := DFunLike.congr_fun h2 f
    simp only [AlgHom.comp_apply] at e1 e2
    rw [e1, e2, hf.2 l j hlj]

def rhoNu {r r' n : ℕ} (ν : Fin n → ℕ) (x : Matrix (Fin r') (Fin r) ℂ) :
    dualWeyl ℂ r n ν →ₗ[ℂ] dualWeyl ℂ r' n ν :=
  (substTr n x).toLinearMap.restrict fun _ hf => substTr_mem ν x hf

def invNorm {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (f : dualWeyl ℂ r n ν) : ℝ :=
  √((fockS f.1 f.1).re / (fockS (hw ℂ hn ν) (hw ℂ hn ν)).re)

def IsOpNorm {r r' n : ℕ} (hn : n ≤ r) (hn' : n ≤ r') (ν : Fin n → ℕ) (x : Matrix (Fin r') (Fin r) ℂ) (c : ℝ) :
    Prop :=
  IsLeast {t : ℝ | 0 ≤ t ∧ ∀ f : dualWeyl ℂ r n ν, invNorm hn' ν (rhoNu ν x f) ≤ t * invNorm hn ν f} c

def singVal {n r' : ℕ} (x : Matrix (Fin r') (Fin n) ℂ) (i : Fin n) : ℝ :=
  (Matrix.toEuclideanLin x : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin r')).singularValues i.val

def PolyFunctorOpNorm : Prop :=
  ∀ (n₀ n₁ : ℕ) (h : n₀ ≤ n₁) (ν : Fin n₀ → ℕ), Antitone ν → ∀ x : Matrix (Fin n₁) (Fin n₀) ℂ,
    IsOpNorm le_rfl h ν x (∏ i, singVal x i ^ ν i) ∧
    IsOpNorm le_rfl h ν (x.map (starRingEnd ℂ)) (∏ i, singVal x i ^ ν i)

theorem substTr_mul {r r' r'' n : ℕ} (x' : Matrix (Fin r'') (Fin r') ℂ) (x : Matrix (Fin r') (Fin r) ℂ) :
    substTr n (x' * x) = (substTr n x').comp (substTr n x) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [substTr, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, Matrix.mul_apply, algebraMap_eq,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem substTr_vec {r r' n : ℕ} (x : Matrix (Fin r') (Fin r) ℂ) (v : Fin r → ℂ) (s : Fin n) :
    substTr n x (∑ a, C (v a) * X (a, s)) = ∑ b, C ((x *ᵥ v) b) * X (b, s) := by
  simp only [substTr, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem fockS_re_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (fockS f f).re := by
  unfold fockS
  rw [Complex.re_sum]
  refine Finset.sum_pos (fun m hm => ?_) (support_nonempty.mpr hf)
  have hc : f.coeff m ≠ 0 := mem_support_iff.mp hm
  have hm0 : 0 < mfact m := Finset.prod_pos fun k _ => Nat.factorial_pos _
  have e : star (f.coeff m) * f.coeff m * (mfact m : ℂ) = ((Complex.normSq (f.coeff m) * mfact m : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]; simp
  rw [e, Complex.ofReal_re]
  exact mul_pos (Complex.normSq_pos.mpr hc) (by exact_mod_cast hm0)

theorem invNorm_hw {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    invNorm hn ν ⟨hw ℂ hn ν, hwMem ℂ r n hn ν hν⟩ = 1 := by
  rw [invNorm, div_self (fockS_re_pos (hwNe ℂ r n hn ν)).ne', Real.sqrt_one]

end GlobalTheory.IndefiniteRowSideFullHecke.TraceSubstitution
