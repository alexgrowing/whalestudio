import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe

open MvPolynomial

namespace GlobalTheory.SubstCoeff

variable {σ : Type}

theorem continuous_coeff_mul {Y : Type} [TopologicalSpace Y] (F G : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => coeff m (F y)) (hG : ∀ m, Continuous fun y => coeff m (G y)) (m : σ →₀ ℕ) :
    Continuous fun y => coeff m (F y * G y) := by
  classical
  simp only [coeff_mul]
  exact continuous_finset_sum _ fun x _ => (hF _).mul (hG _)

theorem continuous_coeff_pow {Y : Type} [TopologicalSpace Y] (F : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => coeff m (F y)) (e : ℕ) (m : σ →₀ ℕ) :
    Continuous fun y => coeff m (F y ^ e) := by
  induction e generalizing m with
  | zero =>
    classical
    simp only [pow_zero, coeff_one]
    exact continuous_const
  | succ e ih =>
    simp only [pow_succ]
    exact continuous_coeff_mul _ _ ih hF m

theorem continuous_coeff_prod {Y κ : Type} [TopologicalSpace Y] (s : Finset κ) (f : κ → Y → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, Continuous fun y => coeff m (f q y)) (m : σ →₀ ℕ) :
    Continuous fun y => coeff m (∏ q ∈ s, f q y) := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty =>
    simp only [Finset.prod_empty, coeff_one]
    exact continuous_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact continuous_coeff_mul _ _ (hf a (Finset.mem_insert_self a s))
      (fun m' => ih (fun q hq => hf q (Finset.mem_insert_of_mem hq)) m') m

theorem isAlgebraic_sum {κ : Type} (s : Finset κ) (f : κ → ℂ) (hf : ∀ q ∈ s, IsAlgebraic ℚ (f q)) :
    IsAlgebraic ℚ (∑ q ∈ s, f q) :=
  Finset.sum_induction f (IsAlgebraic ℚ) (fun _ _ ha hb => ha.add hb) isAlgebraic_zero hf

theorem isAlgebraic_coeff_mul (P Q : MvPolynomial σ ℂ)
    (hP : ∀ m, IsAlgebraic ℚ (coeff m P)) (hQ : ∀ m, IsAlgebraic ℚ (coeff m Q)) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (coeff m (P * Q)) := by
  classical
  rw [coeff_mul]
  exact isAlgebraic_sum _ _ fun x _ => (hP _).mul (hQ _)

theorem isAlgebraic_coeff_one (m : σ →₀ ℕ) : IsAlgebraic ℚ (coeff m (1 : MvPolynomial σ ℂ)) := by
  classical
  rw [coeff_one]
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

theorem isAlgebraic_coeff_pow (P : MvPolynomial σ ℂ)
    (hP : ∀ m, IsAlgebraic ℚ (coeff m P)) (e : ℕ) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (coeff m (P ^ e)) := by
  induction e generalizing m with
  | zero => simpa only [pow_zero] using isAlgebraic_coeff_one m
  | succ e ih =>
    rw [pow_succ]
    exact isAlgebraic_coeff_mul _ _ ih hP m

theorem isAlgebraic_coeff_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, IsAlgebraic ℚ (coeff m (f q))) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (coeff m (∏ q ∈ s, f q)) :=
  Finset.prod_induction f (fun P => ∀ m, IsAlgebraic ℚ (coeff m P))
    (fun _ _ ha hb => isAlgebraic_coeff_mul _ _ ha hb) isAlgebraic_coeff_one hf m

variable {ι : Type} {N n : ℕ}

theorem substF_monomial_one (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF h g (monomial k 1) = ∏ q ∈ k.support, (GlobalTheory.CompactHowe.substF h g (X q)) ^ k q := by
  rw [monomial_eq, map_mul, C_1, map_one, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow]

theorem continuous_coeff_substF_X (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    Continuous fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) =>
      coeff m (GlobalTheory.CompactHowe.substF p.1 p.2 (X q)) := by
  simp only [GlobalTheory.CompactHowe.substF_X, coeff_sum, coeff_C_mul]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  refine Continuous.mul (Continuous.mul ?_ ?_) continuous_const
  · exact ((continuous_apply q.1).comp continuous_fst).matrix_elem a q.2.1
  · exact ((continuous_apply q.1).comp continuous_snd).matrix_elem b q.2.2

theorem isAlgebraic_coeff_substF_X (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hh : ∀ i a b, IsAlgebraic ℚ (h i a b)) (hg : ∀ i a b, IsAlgebraic ℚ (g i a b))
    (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    IsAlgebraic ℚ (coeff m (GlobalTheory.CompactHowe.substF h g (X q))) := by
  classical
  simp only [GlobalTheory.CompactHowe.substF_X, coeff_sum, coeff_C_mul]
  refine isAlgebraic_sum _ _ fun a _ => isAlgebraic_sum _ _ fun b _ => ?_
  refine ((hh _ _ _).mul (hg _ _ _)).mul ?_
  rw [coeff_X']
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

theorem coeff_substF_monomial_continuous_algebraic :
    ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1))) ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (MvPolynomial.coeff k' (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1))) := by
  intro ι N n k k'
  refine ⟨?_, fun h g hh hg => ?_⟩
  · simp only [substF_monomial_one]
    exact continuous_coeff_prod _ _ (fun q _ m => continuous_coeff_pow _ (continuous_coeff_substF_X q) _ m) k'
  · rw [substF_monomial_one]
    exact isAlgebraic_coeff_prod _ _
      (fun q _ m => isAlgebraic_coeff_pow _ (isAlgebraic_coeff_substF_X h g hh hg q) _ m) k'

end GlobalTheory.SubstCoeff
