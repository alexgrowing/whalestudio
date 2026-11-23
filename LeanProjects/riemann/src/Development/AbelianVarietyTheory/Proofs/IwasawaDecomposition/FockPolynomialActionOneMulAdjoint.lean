import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau

noncomputable section

namespace GlobalTheory.JointHarm.FMul

open MvPolynomial Matrix Formalism.L2.DIV

section Lin

variable {σ : Type} [Fintype σ]

def lsub (M : Matrix σ σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => ∑ w, C (M w v) * X w

theorem lsub_X (M : Matrix σ σ ℂ) (v : σ) : lsub M (X v) = ∑ w, C (M w v) * X w := aeval_X _ _

theorem lsub_one [DecidableEq σ] : lsub (1 : Matrix σ σ ℂ) = AlgHom.id ℂ _ := by
  refine algHom_ext fun v => ?_
  rw [lsub_X, Finset.sum_eq_single v]
  · simp
  · intro w _ hw
    simp [Matrix.one_apply_ne hw]
  · simp

theorem lsub_mul (M N : Matrix σ σ ℂ) : lsub (M * N) = (lsub M).comp (lsub N) := by
  refine algHom_ext fun v => ?_
  simp only [AlgHom.comp_apply, lsub_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => ?_
  ring

theorem constantCoeff_lsub (M : Matrix σ σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (lsub M g) = constantCoeff g := by
  have : (constantCoeff : MvPolynomial σ ℂ →+* ℂ).comp (lsub M).toRingHom = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp [lsub_X]
  exact congrArg (fun φ : MvPolynomial σ ℂ →+* ℂ => φ g) this

theorem pderiv_lsub [DecidableEq σ] (M : Matrix σ σ ℂ) (s : σ) (g : MvPolynomial σ ℂ) :
    pderiv s (lsub M g) = ∑ w, C (M s w) * lsub M (pderiv w g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hX : pderiv s (lsub M (X k)) = C (M s k) := by
      rw [lsub_X, map_sum, Finset.sum_eq_single s]
      · simp [pderiv_X]
      · intro b _ hb
        rw [Derivation.leibniz, pderiv_C, pderiv_X_of_ne hb]
        simp
      · simp
    rw [map_mul, Derivation.leibniz, hX, hp, smul_eq_mul, smul_eq_mul]
    simp_rw [Derivation.leibniz, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single k]
      · rw [pderiv_X_self, map_one]; ring
      · intro b _ hb
        rw [pderiv_X_of_ne hb.symm]
        simp
      · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem fockL_lsub_adj (M : Matrix σ σ ℂ) (F F' : MvPolynomial σ ℂ) :
    fockL (lsub M F) F' = fockL F (lsub Mᴴ F') := by
  classical
  induction F using MvPolynomial.induction_on generalizing F' with
  | C a => rw [algHom_C, algebraMap_eq, fockL_C_left, fockL_C_left, constantCoeff_lsub]
  | add p q hp hq => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  | mul_X p v hp =>
    have e1 : lsub M (p * X v) = ∑ w, M w v • (X w * lsub M p) := by
      rw [map_mul, lsub_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]; ring
    rw [e1, map_sum, LinearMap.sum_apply]
    simp_rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, fockL_X_pderiv, hp]
    rw [mul_comm p, fockL_X_pderiv, pderiv_lsub, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, map_smul, Matrix.conjTranspose_apply, starRingEnd_apply]

end Lin

section Blocks

variable {m n : ℕ}

theorem entry_eq_zero {ε : Fin m → Bool} {k : Matrix (Fin m) (Fin m) ℂ}
    (h : k * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k) {a i : Fin m} (hai : ε a ≠ ε i) : k a i = 0 := by
  have h1 := congrFun (congrFun h a) i
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  cases ha : ε a <;> cases hi : ε i <;> simp only [ha, hi] at hai h1 <;> simp at hai h1
  · linear_combination (1 / 2 : ℂ) * h1
  · linear_combination (-1 / 2 : ℂ) * h1

theorem inv_comm {ε : Fin m → Bool} {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ GlobalTheory.Dec.KC ε) :
    k⁻¹ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det k).1 hk.1
  calc k⁻¹ * Formalism.REAL.Jm ε = k⁻¹ * (Formalism.REAL.Jm ε * k) * k⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    _ = Formalism.REAL.Jm ε * k⁻¹ := by
        rw [← hk.2, ← Matrix.mul_assoc k⁻¹, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

theorem Jm_mul_Jm (ε : Fin m → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases ε a <;> simp

theorem Jm_conj (ε : Fin m → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  cases h : ε a <;> simp [h]

def blk (J k : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (1 / 2 : ℂ) • (1 + J) * k + (1 / 2 : ℂ) • (1 - J)

theorem blk_one (J : Matrix (Fin m) (Fin m) ℂ) : blk J 1 = 1 := by
  rw [blk, Matrix.mul_one, ← smul_add, add_add_sub_cancel, ← two_smul ℂ, smul_smul]
  simp

theorem blk_mul {J k : Matrix (Fin m) (Fin m) ℂ} (hJ : J * J = 1) (hk : k * J = J * k)
    (k' : Matrix (Fin m) (Fin m) ℂ) : blk J (k * k') = blk J k * blk J k' := by
  have h1 : ∀ x : Matrix (Fin m) (Fin m) ℂ, J * (J * x) = x := fun x => by
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have h2 : ∀ x : Matrix (Fin m) (Fin m) ℂ, k * (J * x) = J * (k * x) := fun x => by
    rw [← Matrix.mul_assoc, hk, Matrix.mul_assoc]
  simp only [blk, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    mul_assoc, h1, h2, hJ, hk, smul_add, smul_sub]
  module

theorem blk_conj {J k : Matrix (Fin m) (Fin m) ℂ} (hJ : Jᴴ = J) (hk : k * J = J * k) :
    blk J kᴴ = (blk J k)ᴴ := by
  have h1 : kᴴ * J = J * kᴴ := by
    have := congrArg Matrix.conjTranspose hk
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ] at this
    exact this.symm
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [blk, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hJ, h2, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add,
    one_mul, mul_one, h1]

theorem detPlus_def₂ (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) :
    detP ε k = (blk (Formalism.REAL.Jm ε) k).det := rfl

theorem detM_eq (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) :
    detM ε k = (blk (-Formalism.REAL.Jm ε) k).det := by
  rw [detM, blk, sub_neg_eq_add, ← sub_eq_add_neg]

variable {ι : Type} [DecidableEq ι]

def fmat (ε : ι → Fin m → Bool) (k : ι → Matrix (Fin m) (Fin m) ℂ) (u : ι → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (ι × Fin m × Fin n) (ι × Fin m × Fin n) ℂ :=
  Matrix.of fun w v => if w.1 = v.1 then
    (if ε v.1 v.2.1 = true then k v.1 w.2.1 v.2.1 * (u v.1)⁻¹ v.2.2 w.2.2
      else (k v.1)⁻¹ v.2.1 w.2.1 * u v.1 w.2.2 v.2.2) else 0

theorem fmat_one (ε : ι → Fin m → Bool) : fmat (n := n) ε 1 1 = 1 := by
  ext ⟨s, a, b⟩ ⟨t, i, j⟩
  simp only [fmat, Matrix.of_apply, Pi.one_apply, inv_one, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : s = t <;> by_cases h2 : a = i <;> by_cases h3 : b = j <;>
    simp [h1, h2, h3, eq_comm (a := i), eq_comm (a := j)]

theorem fmat_mul [Fintype ι] (ε : ι → Fin m → Bool) (k k' : ι → Matrix (Fin m) (Fin m) ℂ)
    (u u' : ι → Matrix (Fin n) (Fin n) ℂ) (hk' : ∀ τ, k' τ ∈ GlobalTheory.Dec.KC (ε τ)) :
    fmat ε (k * k') (u * u') = fmat ε k u * fmat ε k' u' := by
  ext ⟨s, a, b⟩ ⟨t, i, j⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single t]
  · simp only [fmat, Matrix.of_apply, Pi.mul_apply, Matrix.mul_inv_rev, if_true]
    by_cases h1 : s = t
    · simp only [h1, if_true]
      rw [Fintype.sum_prod_type]
      cases hi : ε t i
      · simp only [Bool.false_eq_true, if_false, Matrix.mul_apply, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        cases hc : ε t c
        · simp only [Bool.false_eq_true, if_false]; ring
        · rw [entry_eq_zero (inv_comm (hk' t)) (a := i) (i := c) (by simp [hi, hc])]; simp
      · simp only [if_true, Matrix.mul_apply, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        cases hc : ε t c
        · rw [entry_eq_zero (hk' t).2 (a := c) (i := i) (by simp [hi, hc])]; simp
        · simp only [if_true]; ring
    · simp [h1]
  · intro r _ hr
    simp [fmat, hr]
  · simp

theorem fmat_conj (ε : ι → Fin m → Bool) (k : ι → Matrix (Fin m) (Fin m) ℂ)
    (u : ι → Matrix (Fin n) (Fin n) ℂ) (hk : ∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) :
    fmat ε (fun τ => (k τ)ᴴ) (fun τ => (u τ)ᴴ) = (fmat ε k u)ᴴ := by
  ext ⟨s, a, b⟩ ⟨t, i, j⟩
  simp only [fmat, Matrix.of_apply, Matrix.conjTranspose_apply, ← Matrix.conjTranspose_nonsing_inv]
  by_cases h1 : s = t
  · subst h1
    simp only [if_true]
    cases hi : ε s i <;> cases ha : ε s a
    · simp
    · rw [entry_eq_zero (hk s).2 (a := i) (i := a) (by simp [hi, ha]),
        entry_eq_zero (inv_comm (hk s)) (a := a) (i := i) (by simp [hi, ha])]
      simp
    · rw [entry_eq_zero (hk s).2 (a := i) (i := a) (by simp [hi, ha]),
        entry_eq_zero (inv_comm (hk s)) (a := a) (i := i) (by simp [hi, ha])]
      simp
    · simp
  · simp [h1, Ne.symm h1]

end Blocks

end GlobalTheory.JointHarm.FMul

namespace GlobalTheory.JointHarm

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {m n : ℕ}

theorem fsub_eq_lsub (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : fsub ε k u = FMul.lsub (FMul.fmat ε k u) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [FMul.lsub_X, fsub, MvPolynomial.aeval_X, Fintype.sum_prod_type, Finset.sum_eq_single v.1,
    Fintype.sum_prod_type]
  · simp only [FMul.fmat, Matrix.of_apply, if_true]
  · intro r _ hr
    simp [FMul.fmat, hr]
  · simp

theorem fchar_one (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ) :
    fchar (n := n) ε x₁ x₂ x₃ 1 1 = 1 := by
  simp [fchar, FMul.detPlus_def₂, FMul.detM_eq, FMul.blk_one]

theorem fchar_mul (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (k k' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u u' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (hk : ∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) :
    fchar ε x₁ x₂ x₃ (k * k') (u * u') = fchar ε x₁ x₂ x₃ k u * fchar ε x₁ x₂ x₃ k' u' := by
  unfold fchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [FMul.detPlus_def₂, FMul.detM_eq, Pi.mul_apply]
  rw [FMul.blk_mul (FMul.Jm_mul_Jm _) (hk τ).2,
    FMul.blk_mul (J := -Formalism.REAL.Jm (ε τ)) (by rw [neg_mul_neg, FMul.Jm_mul_Jm])
      (by rw [mul_neg, neg_mul, (hk τ).2])]
  simp only [Matrix.det_mul, mul_zpow]
  ring

theorem fchar_conj (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (hk : ∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) :
    fchar ε x₁ x₂ x₃ (fun τ => (k τ)ᴴ) (fun τ => (u τ)ᴴ) = star (fchar ε x₁ x₂ x₃ k u) := by
  unfold fchar
  rw [star_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [FMul.detPlus_def₂, FMul.detM_eq]
  rw [FMul.blk_conj (FMul.Jm_conj _) (hk τ).2,
    FMul.blk_conj (J := -Formalism.REAL.Jm (ε τ)) (by rw [Matrix.conjTranspose_neg, FMul.Jm_conj])
      (by rw [mul_neg, neg_mul, (hk τ).2])]
  simp only [Matrix.det_conjTranspose, star_mul', star_zpow₀]

end

theorem fact_one_mul_adj : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), fact (n := n) ε x₁ x₂ x₃ 1 1 = 1 ∧ (∀ (k k' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u u' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, k' τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, IsUnit (u τ)) → (∀ τ, IsUnit (u' τ)) → fact ε x₁ x₂ x₃ (k * k') (u * u') = fact ε x₁ x₂ x₃ k u * fact ε x₁ x₂ x₃ k' u') ∧ ∀ (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, IsUnit (u τ)) → ∀ F F' : PolF D m n, fockL (fact ε x₁ x₂ x₃ k u F) F' = fockL F (fact ε x₁ x₂ x₃ (fun τ => (k τ)ᴴ) (fun τ => (u τ)ᴴ) F') := by
  intro D m n ε x₁ x₂ x₃
  refine ⟨?_, fun k k' u u' hk hk' _ _ => ?_, fun k u hk _ F F' => ?_⟩
  · rw [fact, fchar_one, one_smul, fsub_eq_lsub, FMul.fmat_one, FMul.lsub_one]
    rfl
  · simp only [fact]
    rw [fchar_mul ε x₁ x₂ x₃ k k' u u' hk, smul_mul_smul_comm, fsub_eq_lsub, fsub_eq_lsub, fsub_eq_lsub,
      FMul.fmat_mul ε k k' u u' hk', FMul.lsub_mul]
    rfl
  · simp only [fact]
    rw [fchar_conj ε x₁ x₂ x₃ k u hk, fsub_eq_lsub, fsub_eq_lsub, FMul.fmat_conj ε k u hk]
    simp only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, LinearMap.map_smulₛₗ, starRingEnd_apply,
      RingHom.id_apply, FMul.fockL_lsub_adj]

end GlobalTheory.JointHarm

end
