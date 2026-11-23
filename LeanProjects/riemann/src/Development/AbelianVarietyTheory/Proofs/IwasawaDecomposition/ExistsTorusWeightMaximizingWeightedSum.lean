import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW.MaxWeight

noncomputable def twoDiag (n : ℕ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal (fun i : Fin n => (2 : ℂ) ^ ((n : ℤ) - ((i : ℕ) : ℤ))),
    Matrix.diagonal (fun i : Fin n => ((2 : ℂ) ^ ((n : ℤ) - ((i : ℕ) : ℤ)))⁻¹),
    by
      rw [Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (zpow_ne_zero _ two_ne_zero),
    by
      rw [Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (zpow_ne_zero _ two_ne_zero)⟩

lemma twoDiag_isDiag (n : ℕ) : (twoDiag n).val.IsDiag := Matrix.isDiag_diagonal _

lemma prod_two_zpow {n : ℕ} (ν : Fin n → ℤ) (s : Finset (Fin n)) :
    ∏ i ∈ s, ((2 : ℂ) ^ ((n : ℤ) - ((i : ℕ) : ℤ))) ^ (ν i) =
      (2 : ℂ) ^ (∑ i ∈ s, ((n : ℤ) - ((i : ℕ) : ℤ)) * ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ two_ne_zero, ← _root_.zpow_mul]

lemma two_zpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have h' : ((2 : ℝ) ^ a : ℝ) = (2 : ℝ) ^ b := by
    have ha : ((2 : ℂ) ^ a) = (((2 : ℝ) ^ a : ℝ) : ℂ) := by push_cast; rfl
    have hb : ((2 : ℂ) ^ b) = (((2 : ℝ) ^ b : ℝ) : ℂ) := by push_cast; rfl
    rw [ha, hb] at h
    exact_mod_cast h
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h'

theorem exists_max_weight : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ₀ : Fin n → ℤ), IsWt Φ μ₀ →
    ∃ μ : Fin n → ℤ, IsWt Φ μ ∧ ∀ ν : Fin n → ℤ, IsWt Φ ν →
      ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * ν i ≤ ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * μ i := by
  intro n ι _ _ Φ μ₀ h₀
  let f : (Fin n → ℤ) → ℤ := fun ν => ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * ν i
  let A : Module.End ℂ (ι → ℂ) := Matrix.toLin' (Φ (twoDiag n))
  have heig : ∀ ν, IsWt Φ ν → A.HasEigenvalue ((2 : ℂ) ^ f ν) := by
    rintro ν ⟨w, hw0, hw⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := w)
    refine ⟨?_, hw0⟩
    rw [Module.End.mem_eigenspace_iff]
    simp only [A, Matrix.toLin'_apply]
    rw [hw _ (twoDiag_isDiag n)]
    congr 1
    rw [← prod_two_zpow ν Finset.univ]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [twoDiag, Matrix.diagonal_apply_eq]
  let S : Set ℤ := {k | ∃ ν, IsWt Φ ν ∧ f ν = k}
  have hfin : S.Finite := by
    have hF := Module.End.finite_hasEigenvalue A
    refine (hF.preimage (f := fun k : ℤ => (2 : ℂ) ^ k) (fun a _ b _ h => two_zpow_inj h)).subset ?_
    rintro k ⟨ν, hν, rfl⟩
    exact heig ν hν
  obtain ⟨B, hB⟩ := hfin.bddAbove
  obtain ⟨m, ⟨μ, hμ, rfl⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd (P := fun k => k ∈ S) ⟨B, fun z hz => hB hz⟩ ⟨f μ₀, μ₀, h₀, rfl⟩
  exact ⟨μ, hμ, fun ν hν => hmax _ ⟨ν, hν, rfl⟩⟩

end GlobalTheory.AlgWtHW.MaxWeight
