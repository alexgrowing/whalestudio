import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn GlobalTheory.CompanionTheory.ThTot
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.Orb
variable {D : D7}

def fro {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem fro_nonneg {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : 0 ≤ fro A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem fro_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin b) (Fin c) ℂ) :
    fro (A * B) ≤ fro A * fro B := by
  have key : ∀ i j, ‖(A * B) i j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := by
      rw [Matrix.mul_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖A i k‖) (fun k => ‖B k j‖)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  unfold fro
  calc ∑ i, ∑ j, ‖(A * B) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ k, ∑ j, ‖B k j‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]

theorem norm_entry_sq_le {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (i : Fin a) (j : Fin b) :
    ‖A i j‖ ^ 2 ≤ fro A := by
  unfold fro
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖ ^ 2) (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)

theorem continuous_fro {a b : ℕ} : Continuous (fro : Matrix (Fin a) (Fin b) ℂ → ℝ) := by
  unfold fro
  fun_prop

theorem trace_conjTranspose_mul_self {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) :
    Matrix.trace (Aᴴ * A) = ((fro A : ℝ) : ℂ) := by
  unfold fro
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_mul']
  rfl

def nrm {m : ℕ} {n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ τ, |l τ| * fro (z τ)

theorem nrm_nonneg {m n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : 0 ≤ nrm l z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (fro_nonneg _)

theorem entry_le_nrm {m n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (τ) (i j) :
    |l τ| * ‖z τ i j‖ ^ 2 ≤ nrm l z := by
  refine le_trans (mul_le_mul_of_nonneg_left (norm_entry_sq_le _ i j) (abs_nonneg _)) ?_
  exact Finset.single_le_sum (f := fun τ => |l τ| * fro (z τ)) (fun _ _ => mul_nonneg (abs_nonneg _) (fro_nonneg _)) (Finset.mem_univ τ)

theorem norm_le_exp {w : ℂ} {d : ℝ} (hd : 0 < d) : ‖w‖ ≤ (1 / Real.sqrt d) * Real.exp (d * ‖w‖ ^ 2) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have h1 : Real.sqrt d * ‖w‖ ≤ Real.exp (d * ‖w‖ ^ 2) := by
    have h2 : d * ‖w‖ ^ 2 + 1 ≤ Real.exp (d * ‖w‖ ^ 2) := Real.add_one_le_exp _
    have h3 : (Real.sqrt d * ‖w‖) ^ 2 = d * ‖w‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hd.le]
    nlinarith [sq_nonneg (Real.sqrt d * ‖w‖ - 1)]
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hs]
  linarith [mul_comm (Real.sqrt d) ‖w‖]

theorem evalPoly_bound {m n : ℕ} (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    ∀ e : ℝ, 0 < e → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ,
      ‖evalPoly q z‖ ≤ C * Real.exp (e * nrm l z) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    intro e he
    refine ⟨‖a‖, norm_nonneg _, fun z => ?_⟩
    simp only [evalPoly, MvPolynomial.eval_C]
    have : 1 ≤ Real.exp (e * nrm l z) := Real.one_le_exp (mul_nonneg he.le (nrm_nonneg _ _))
    nlinarith [norm_nonneg a]
  | add p q hp hq =>
    intro e he
    obtain ⟨C₁, h₁, b₁⟩ := hp e he
    obtain ⟨C₂, h₂, b₂⟩ := hq e he
    refine ⟨C₁ + C₂, add_nonneg h₁ h₂, fun z => ?_⟩
    have : evalPoly (p + q) z = evalPoly p z + evalPoly q z := by simp [evalPoly]
    rw [this, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (b₁ z) (b₂ z))
  | mul_X p k hp =>
    intro e he
    obtain ⟨C₁, h₁, b₁⟩ := hp (e / 2) (by positivity)
    obtain ⟨τ, i, j, b⟩ := k
    have hlt : 0 < |l τ| := abs_pos.2 (hl τ)
    set d : ℝ := e / 2 * |l τ| with hd
    have hd0 : 0 < d := by positivity
    refine ⟨C₁ * (1 / Real.sqrt d), by positivity, fun z => ?_⟩
    have hm : evalPoly (p * MvPolynomial.X (τ, i, j, b)) z = evalPoly p z *
        (if b then conj (z τ i j) else z τ i j) := by simp [evalPoly]
    have hx : ‖(if b then conj (z τ i j) else z τ i j)‖ = ‖z τ i j‖ := by
      split_ifs <;> simp
    rw [hm, norm_mul, hx]
    have h1 := norm_le_exp (w := z τ i j) hd0
    have h2 : Real.exp (d * ‖z τ i j‖ ^ 2) ≤ Real.exp (e / 2 * nrm l z) := by
      apply Real.exp_le_exp.2
      have := entry_le_nrm l z τ i j
      rw [hd, mul_assoc]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : ‖z τ i j‖ ≤ (1 / Real.sqrt d) * Real.exp (e / 2 * nrm l z) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    calc ‖evalPoly p z‖ * ‖z τ i j‖
        ≤ (C₁ * Real.exp (e / 2 * nrm l z)) * ((1 / Real.sqrt d) * Real.exp (e / 2 * nrm l z)) :=
          mul_le_mul (b₁ z) h3 (norm_nonneg _) (by positivity)
      _ = C₁ * (1 / Real.sqrt d) * Real.exp (e * nrm l z) := by
          have : Real.exp (e * nrm l z) = Real.exp (e / 2 * nrm l z) * Real.exp (e / 2 * nrm l z) := by
            rw [← Real.exp_add]; ring_nf
          rw [this]; ring

end GlobalTheory.CompanionTheory.ThTot.Orb

end
