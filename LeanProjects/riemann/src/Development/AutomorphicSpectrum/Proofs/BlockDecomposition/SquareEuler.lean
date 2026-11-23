import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasProdMoebiusConvOfNormLe

open Ad3 Ad3.S LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace GlobalTheory.CompanionTheory.SquareEuler

lemma term_coeff_eq (h1 : N1) {M : ℕ} (c : DirichletCharacter ℂ M) (n : ℤ) (s : ℂ) (d : ℕ) :
    c (d : ZMod M) * RR n d * (d : ℂ) ^ (-(s + 1)) =
      LSeries.term (↗c * ((↗μ : ℕ → ℂ) ⍟ (fun e => (NN n e : ℂ)))) s d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [RR]
  · rw [LSeries.term_of_ne_zero hd.ne', h1 n d hd, LSeries.convolution_def]
    simp only [Pi.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => ((μ a : ℤ) : ℂ) * (NN n b : ℂ))]
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hp : (d : ℂ) ^ (-(s + 1)) = ((d : ℂ) ^ s)⁻¹ * (d : ℂ)⁻¹ := by
      rw [show -(s + 1) = -s + -1 by ring, Complex.cpow_add _ _ hd0, Complex.cpow_neg_one,
        Complex.cpow_neg]
    rw [hp]
    have hds : (d : ℂ) ^ s ≠ 0 := by simp [hd0]
    field_simp

theorem euler_coeff : N1 → N2 → A2 := by
  intro h1 h2 M _ c n s hs
  set N : ℕ → ℂ := fun e => (NN n e : ℂ)
  have hNle : ∀ d : ℕ, d ≠ 0 → ‖N d‖ ≤ d := fun d _ => by
    simp only [N, Complex.norm_natCast]; exact_mod_cast (h2 n).2.1 d
  have hNs : LSeriesSummable N s := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 2) hs ⟨1, fun d hd => ?_⟩
    have : (d : ℝ) ^ ((2 : ℝ) - 1) = d := by norm_num
    rw [this, one_mul]
    exact hNle d hd
  have hμs : LSeriesSummable (↗μ : ℕ → ℂ) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by linarith)
  have hconv : LSeriesSummable ((↗μ : ℕ → ℂ) ⍟ N) s := hμs.convolution hNs
  have hT := DirichletCharacter.LSeriesSummable_mul c hconv
  refine ⟨?_, ?_⟩
  · exact hT.norm.congr fun d => by rw [term_coeff_eq h1 c n s d]
  · have hD : Dn c n s = L (↗c * ((↗μ : ℕ → ℂ) ⍟ N)) s := tsum_congr (term_coeff_eq h1 c n s)
    have hL : DirichletCharacter.LFunction (c ^ 2) (2 * s) = L ↗(c ^ 2) (2 * s) :=
      DirichletCharacter.LFunction_eq_LSeries _ (by rw [Complex.mul_re]; norm_num; linarith)
    rw [hD, hL, mul_comm]
    refine hasProd_moebius_conv_of_norm_le c (N := N) (by simp [N, (h2 n).1]) ?_ hNle hs
    intro a b hab
    simp only [N, (h2 n).2.2.1 a b hab, Nat.cast_mul]

end GlobalTheory.CompanionTheory.SquareEuler
