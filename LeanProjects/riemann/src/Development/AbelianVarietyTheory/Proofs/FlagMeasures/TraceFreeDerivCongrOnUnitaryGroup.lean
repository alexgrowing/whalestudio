import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.DSSU.Local

variable {n : ℕ}

theorem trace_traceFreeMatrixUnit_eq_zero (a b : Fin n) : (E0 a b).trace = 0 := by
  have hn : (n : ℂ) ≠ 0 := by
    have : 0 < n := Fin.pos a
    exact_mod_cast this.ne'
  unfold E0
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  by_cases h : a = b
  · subst h
    simp [hn]
  · simp [h, Matrix.trace_single_eq_of_ne _ _ _ h]

theorem trace_theta (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.trace = 0) :
    (Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε).trace = 0 := by
  rw [Matrix.trace_mul_cycle, Formalism.REAL.Jm_mul_self, Matrix.one_mul, Matrix.trace_conjTranspose, hZ, star_zero]

theorem trace_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.trace = 0) :
    (cpart1 ε Z).trace = 0 := by
  unfold cpart1
  rw [Matrix.trace_smul, Matrix.trace_sub, trace_theta ε Z hZ, hZ, sub_zero, smul_zero]

theorem trace_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.trace = 0) :
    (cpart2 ε Z).trace = 0 := by
  unfold cpart2
  rw [Matrix.trace_smul, Matrix.trace_add, trace_theta ε Z hZ, hZ, add_zero, smul_zero]

theorem mul_exp_mem (ε : Fin n → Bool) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (h0 : X.trace = 0)
    (hg : g ∈ SUset ε) (t : ℝ) : g * NormedSpace.exp ((t : ℂ) • X) ∈ SUset ε := by
  refine ⟨indefinite_unitary_mul_mem ε hg.1 (exp_indefinite_unitary_holds n ε X hX t), ?_⟩
  rw [Matrix.det_mul, hg.2, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, h0, smul_zero, Complex.exp_zero, one_mul]

theorem rd_congr (ε : Fin n → Bool) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (h0 : X.trace = 0)
    {G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g ∈ SUset ε, G₁ g = G₂ g) (hg : g ∈ SUset ε) :
    Rd X G₁ g = Rd X G₂ g := by
  unfold Rd
  congr 1
  funext t
  exact h _ (mul_exp_mem ε hX h0 hg t)

theorem matrix_unit_action_congr : ∀ (n : ℕ) (ε : Fin n → Bool) (G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ) (a b : Fin n),
    (∀ g ∈ SUset ε, G₁ g = G₂ g) → ∀ g ∈ SUset ε, Ec ε (E0 a b) G₁ g = Ec ε (E0 a b) G₂ g := by
  intro n ε G₁ G₂ a b h g hg
  obtain ⟨h1, h2, -⟩ := complex_parts_mem_lie_algebra_holds n ε (E0 a b)
  unfold Ec
  rw [rd_congr ε h1 (trace_cpart1 ε _ (trace_traceFreeMatrixUnit_eq_zero a b)) h hg, rd_congr ε h2 (trace_cpart2 ε _ (trace_traceFreeMatrixUnit_eq_zero a b)) h hg]

end GlobalTheory.DSSU.Local
