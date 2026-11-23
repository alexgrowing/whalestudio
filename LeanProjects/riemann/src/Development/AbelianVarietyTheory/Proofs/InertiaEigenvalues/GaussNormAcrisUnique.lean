import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial

noncomputable section

open scoped Formalism.Per
open Filter Topology

namespace GlobalTheory.PMon.Gauss

theorem abs_sub_le_of_le_max {a b t : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ max b t) (hba : b ≤ max a t) :
    |a - b| ≤ t := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (sub_nonpos.2 h)]
    rcases le_max_iff.1 hba with h' | h'
    · linarith
    · linarith
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    rcases le_max_iff.1 hab with h' | h'
    · linarith
    · linarith

variable {l : ℕ} [Fact l.Prime]

theorem isGauss_natCast {ρ : ℝ} (hρ : 0 ≤ ρ) {N : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N) :
    N (l : Formalism.Per.Acris l) = ρ := by
  rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, hN.2.2.2.2]
  exact GlobalTheory.GaussSlope.gauss_l l hρ

theorem isGauss_pow_mul {ρ : ℝ} (hρ : 0 ≤ ρ) {N : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N)
    (k : ℕ) (x : Formalism.Per.Acris l) : N ((l : Formalism.Per.Acris l) ^ k * x) = ρ ^ k * N x := by
  rw [GlobalTheory.GaussSlope.map_pow_mul N hN.2.2.2.1, isGauss_natCast hρ hN]

theorem isGauss_eq_on_acris0 {ρ : ℝ} (hρ : 0 < ρ) {N N' : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N)
    (hN' : IsGauss l ρ N') (s : Formalism.Per.Acris0 l) :
    N (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) =
      N' (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) := by
  obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
  have h1 := congrArg N ha
  have h2 := congrArg N' ha
  rw [isGauss_pow_mul hρ.le hN, hN.2.2.2.2] at h1
  rw [isGauss_pow_mul hρ.le hN', hN'.2.2.2.2] at h2
  have hk : ρ ^ k ≠ 0 := pow_ne_zero _ hρ.ne'
  exact mul_left_cancel₀ hk (h1.trans h2.symm)

theorem isGauss_abs_sub_le {ρ : ℝ} (hρ : 0 ≤ ρ) {N : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N)
    (s z : Formalism.Per.Acris l) (r : ℕ) : |N (s + (l : Formalism.Per.Acris l) ^ r * z) - N s| ≤ ρ ^ r := by
  obtain ⟨h01, hadd, hneg, -, -⟩ := id hN
  have hz : N ((l : Formalism.Per.Acris l) ^ r * z) ≤ ρ ^ r := by
    rw [isGauss_pow_mul hρ hN]
    exact mul_le_of_le_one_right (pow_nonneg hρ _) (h01 z).2
  apply abs_sub_le_of_le_max (pow_nonneg hρ _) (h01 _).1 (h01 _).1
  · exact (hadd _ _).trans (max_le_max le_rfl hz)
  · have := hadd (s + (l : Formalism.Per.Acris l) ^ r * z) (-((l : Formalism.Per.Acris l) ^ r * z))
    rw [add_neg_cancel_right, hneg] at this
    exact this.trans (max_le_max le_rfl hz)

theorem isGauss_unique : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ) (N N' : Formalism.Per.Acris l → ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 →
    IsGauss l ρ N → IsGauss l ρ N' → N = N' := by
  intro l _ ρ N N' hρl hρ1 hN hN'
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ : 0 < ρ := (inv_pos.2 hl).trans_le hρl
  funext x
  have hb : ∀ r : ℕ, |N x - N' x| ≤ 2 * ρ ^ r := by
    intro r
    obtain ⟨s, z, hx⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
    have e := isGauss_eq_on_acris0 hρ hN hN' s
    have h1 := isGauss_abs_sub_le hρ.le hN (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) z r
    have h2 := isGauss_abs_sub_le hρ.le hN' (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) z r
    rw [← hx] at h1 h2
    rw [e] at h1
    calc |N x - N' x| = |(N x - N' (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s)) -
          (N' x - N' (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s))| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ 2 * ρ ^ r := by linarith
  have ht : Tendsto (fun r : ℕ => 2 * ρ ^ r) atTop (𝓝 (2 * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1).const_mul 2
  rw [mul_zero] at ht
  have h0 : |N x - N' x| ≤ 0 := ge_of_tendsto' ht hb
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

end GlobalTheory.PMon.Gauss

end
