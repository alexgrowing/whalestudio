import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.GaussProd

theorem sum_pi_prod {ι Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Q] (g : ι → Q → ℂ) :
    (∑ y : ι → Q, ∏ i, g i (y i)) = ∏ i, ∑ w, g i w := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem chi_sum {ι Q : Type} [AddCommMonoid Q] (χ : AddChar Q ℂ) (s : Finset ι) (g : ι → Q) :
    χ (∑ i ∈ s, g i) = ∏ i ∈ s, χ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem trace_diag {Q : Type} [CommRing Q] (τ : Q →+* Q) (m n : ℕ) (d : Fin n → Q) (e : Fin m → Q)
    (y : Matrix (Fin m) (Fin n) Q) :
    Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y)) =
      ∑ i, ∑ l, e l * d i * (τ (y l i) * y l i) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diagonal_mul, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_diagonal]
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  ring

theorem red_diagonal {R : Type} [CommRing R] (ϖ : R) (k n : ℕ) (D : Fin n → R) :
    red ϖ k (Matrix.diagonal D) =
      Matrix.diagonal fun i => Ideal.Quotient.mk (lev ϖ k) (D i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [red]
  · simp [red, Matrix.diagonal_apply_ne _ h]

theorem sum_fun_prod {Q : Type} [Fintype Q] (m n : ℕ) (f : Fin n → Fin m → Q → ℂ) :
    (∑ y : Fin m → Fin n → Q, ∏ l, ∏ i, f i l (y l i)) = ∏ i, ∏ l, ∑ w, f i l w := by
  have h1 : ∀ l, ∑ v : Fin n → Q, ∏ i, f i l (v i) = ∏ i, ∑ w, f i l w := fun l =>
    sum_pi_prod (fun i => f i l)
  have h2 := sum_pi_prod (ι := Fin m) (Q := Fin n → Q) (fun l v => ∏ i, f i l (v i))
  simp only [h1] at h2
  rw [Finset.prod_comm]
  exact h2

theorem gauss_gen {Q : Type} [CommRing Q] [Fintype Q] (τ : Q →+* Q) (χ : AddChar Q ℂ) (m n : ℕ)
    (d : Fin n → Q) (e : Fin m → Q) :
    (∑ y : Matrix (Fin m) (Fin n) Q,
      χ (Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y)))) =
      ∏ i : Fin n, ∏ l : Fin m, ∑ w : Q, χ (e l * d i * (τ w * w)) := by
  let f : Fin n → Fin m → Q → ℂ := fun i l w => χ (e l * d i * (τ w * w))
  have hterm : ∀ y : Matrix (Fin m) (Fin n) Q,
      χ (Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y))) =
        ∏ l, ∏ i, f i l (y l i) := by
    intro y
    rw [trace_diag, chi_sum, Finset.prod_comm (s := Finset.univ) (t := Finset.univ)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [chi_sum]
  exact (Fintype.sum_equiv Matrix.of.symm _ _ fun y => hterm y).trans (sum_fun_prod m n f)

theorem gauss_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (D : Fin n → R) (E : Fin m → R), (∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k (Matrix.diagonal D) * (cT (barσ σ ϖ hf k) y * red ϖ k (Matrix.diagonal E) * y)))) = ∏ i : Fin n, ∏ l : Fin m, ∑ w : R ⧸ lev ϖ k, χ (Ideal.Quotient.mk (lev ϖ k) (E l * D i) * (barσ σ ϖ hf k w * w)) := by
  intro R _ σ ϖ hf k _ χ m n D E
  have h := gauss_gen (barσ σ ϖ hf k) χ m n (fun i => Ideal.Quotient.mk (lev ϖ k) (D i))
    (fun l => Ideal.Quotient.mk (lev ϖ k) (E l))
  simp only [red_diagonal, map_mul]
  exact h

end GlobalTheory.CompanionTheory.GaussProd
