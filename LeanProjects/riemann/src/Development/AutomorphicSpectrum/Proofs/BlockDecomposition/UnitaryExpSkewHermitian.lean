import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JBConjTranspose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHermitianSimultaneousDiag

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary GlobalTheory.LinRed GlobalTheory.CompanionTheory.GLK
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.UnitaryExp

theorem exists_unitary_diag {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (h1 : Kᴴ * K = 1) (h2 : K * Kᴴ = 1) :
    ∃ (V : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ), Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      Vᴴ * K * V = Matrix.diagonal z ∧ ∀ a, ‖z a‖ = 1 := by
  classical
  set A : Matrix (Fin n) (Fin n) ℂ := K + Kᴴ with hA
  set B : Matrix (Fin n) (Fin n) ℂ := Complex.I • (K - Kᴴ) with hB
  have hAh : Aᴴ = A := by
    simp [hA, Matrix.conjTranspose_add, add_comm]
  have hBh : Bᴴ = B := by
    simp [hB, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, smul_sub]
    abel
  have hAB : A * B = B * A := by
    have e : (K + Kᴴ) * (K - Kᴴ) = (K - Kᴴ) * (K + Kᴴ) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
      abel
    rw [hA, hB, Matrix.mul_smul, Matrix.smul_mul, e]
  obtain ⟨V, hV, hD⟩ := GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag ({A, B} : Set (Matrix (Fin n) (Fin n) ℂ))
    (by
      rintro X (rfl | rfl)
      · exact hAh
      · exact hBh)
    (by
      rintro X (rfl | rfl) Y (rfl | rfl)
      · rfl
      · exact hAB
      · exact hAB.symm
      · rfl)
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hV
  have hV2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hKAB : K = (1 / 2 : ℂ) • (A - Complex.I • B) := by
    simp only [hA, hB, smul_smul, Complex.I_mul_I]
    module
  have hDd : (Vᴴ * K * V).IsDiag := by
    have e : Vᴴ * K * V = (1 / 2 : ℂ) • (Vᴴ * A * V - Complex.I • (Vᴴ * B * V)) := by
      conv_lhs => rw [hKAB]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [e]
    exact ((hD A (by simp)).sub ((hD B (by simp)).smul _)).smul _
  refine ⟨V, Matrix.diag (Vᴴ * K * V), hV1, hV2, hDd.diagonal_diag.symm, fun a => ?_⟩
  set D := Vᴴ * K * V with hDdef
  have hDD : Dᴴ * D = 1 := by
    have e : Dᴴ = Vᴴ * Kᴴ * V := by
      simp [hDdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e, hDdef]
    calc Vᴴ * Kᴴ * V * (Vᴴ * K * V) = Vᴴ * Kᴴ * (V * Vᴴ) * K * V := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * (Kᴴ * K) * V := by
          rw [hV2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hV1]
  have hent : star (D a a) * D a a = 1 := by
    have h := congrFun (congrFun hDD a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h
    · simpa [Matrix.conjTranspose_apply] using h
    · intro b _ hb
      have : D b a = 0 := hDd hb
      simp [this]
    · simp
  have hn : ‖D a a‖ ^ 2 = 1 := by
    have h3 : ((‖D a a‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have := Complex.conj_mul' (D a a)
      push_cast
      rw [← this]
      simpa using hent
    exact_mod_cast h3
  have h0 : 0 ≤ ‖D a a‖ := norm_nonneg _
  show ‖D a a‖ = 1
  nlinarith [sq_nonneg (‖D a a‖ - 1), sq_nonneg (‖D a a‖ + 1)]

theorem exists_skew_exp_eq (n : ℕ) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ X : Mat n, Xᴴ = -X ∧ uG k = expG X 1 := by
  classical
  have h1 : (k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (k : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 k.2
  have h2 : (k : Matrix (Fin n) (Fin n) ℂ) * (k : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.1 k.2
  obtain ⟨V, z, hV1, hV2, hD, hz⟩ := exists_unitary_diag _ h1 h2
  set w : Fin n → ℂ := fun a => (Complex.arg (z a) : ℂ) * Complex.I with hw
  have hexp : ∀ a, NormedSpace.exp (w a) = z a := by
    intro a
    have := Complex.norm_mul_exp_arg_mul_I (z a)
    rw [hz a] at this
    simpa [hw, Complex.exp_eq_exp_ℂ] using this
  have hk : (k : Matrix (Fin n) (Fin n) ℂ) = V * Matrix.diagonal z * Vᴴ := by
    rw [← hD]
    calc (k : Matrix (Fin n) (Fin n) ℂ)
        = (V * Vᴴ) * (k : Matrix (Fin n) (Fin n) ℂ) * (V * Vᴴ) := by
          rw [hV2]; simp
      _ = V * (Vᴴ * (k : Matrix (Fin n) (Fin n) ℂ) * V) * Vᴴ := by
          simp only [Matrix.mul_assoc]
  refine ⟨V * Matrix.diagonal w * Vᴴ, ?_, ?_⟩
  · have hs : star w = -w := by
      funext a
      simp [hw]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]
    have hn : Matrix.diagonal (-w) = -Matrix.diagonal w := (Matrix.diagonal_neg w).symm
    rw [hn, Matrix.neg_mul, Matrix.mul_neg]
  · refine Units.ext ?_
    let Vu : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨V, Vᴴ, hV2, hV1⟩
    have e := Matrix.exp_units_conj Vu (Matrix.diagonal w)
    have e2 : NormedSpace.exp (Matrix.diagonal w) = Matrix.diagonal z := by
      rw [Matrix.exp_diagonal]
      congr 1
      funext a
      rw [Pi.exp_def]
      exact hexp a
    rw [e2] at e
    have e3 : ((expG (V * Matrix.diagonal w * Vᴴ) 1 : G n) : Mat n) =
        NormedSpace.exp (V * Matrix.diagonal w * Vᴴ) := by
      simp
    rw [e3]
    exact hk.trans e.symm

end GlobalTheory.CompanionTheory.UnitaryExp
