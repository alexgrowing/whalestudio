import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantOfLieOneLEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjCompactOfAdmissible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumProdEqPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCVPosIdele
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts

noncomputable section

open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1
open GroundTheory.Automorphic.Reduction (maxCompact)

namespace GlobalTheory.CompanionTheory.PiVec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def cell (ω : Set (GA E n)) (t₀ : ℝ) (m : Fin n → ℤ) : Set (H E n 0) :=
  {y | ∃ b ∈ ω, ∃ x : Fin n → ℝ, admitted t₀ x ∧ (∀ i, (m i : ℝ) ≤ x i ∧ x i ≤ m i + 1) ∧
    ∃ k ∈ maxCompact (K := E) (n := n), y.1 = b * An.tor E x * k}

theorem admissible_coordinates_bounded_rise : AdmLe := by
  intro n t₀ x ht hA i j hij
  have key : ∀ d : ℕ, ∀ i j : Fin n, (j : ℕ) = i + d → x j ≤ x i + d * t₀ := by
    intro d
    induction d with
    | zero =>
      intro i j h
      have : j = i := Fin.ext (by simpa using h)
      simp [this]
    | succ d ih =>
      intro i j h
      have hj : (j : ℕ) < n := j.2
      have h1 := ih i ⟨i + d, by omega⟩ rfl
      have h2 := hA j
      unfold An.sr at h2
      rw [dif_pos ⟨by omega, j.2⟩] at h2
      have e : (⟨(j : ℕ) - 1, by omega⟩ : Fin n) = ⟨i + d, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e] at h2
      simp only [Fin.eta] at h2
      push_cast
      linarith
  have h1 := key (j - i) i j (by have := Fin.le_def.1 hij; omega)
  have h2 : (((j : ℕ) - i : ℕ) : ℝ) ≤ n := by
    have : (j : ℕ) - i ≤ n := by have := j.2; omega
    exact_mod_cast this
  have := mul_le_mul_of_nonneg_right h2 ht
  linarith

end GlobalTheory.CompanionTheory.PiVec

end
