import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLSeriesContinuation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealMulAbsNormCpowEqExpTsum

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in

theorem _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire (K : Type) [Field K] [NumberField K] :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) *
      Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  let X : Ideal (𝓞 K) → ℂ := fun I => if I = ⊥ then 0 else 1
  have hXbot : X ⊥ = 0 := if_pos rfl
  have hXne : ∀ I, I ≠ ⊥ → X I = 1 := fun I hI => if_neg hI
  have hXmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    by_cases hI : I = ⊥
    · simp [X, hI]
    by_cases hJ : J = ⊥
    · simp [X, hJ]
    rw [hXne _ (Ideal.mul_eq_bot.not.mpr (not_or.mpr ⟨hI, hJ⟩)), hXne _ hI, hXne _ hJ, one_mul]
  obtain ⟨Z, hZd, hZ, -⟩ := _root_.GlobalTheory.idealCharacter_LSeries_continuation K ⊤ X (fun _ => 1) top_ne_bot
    hXbot hXmul (fun I hI _ => by rw [hXne I hI, norm_one]) (fun I hI => absurd (sup_top_eq I) hI)
    (fun _ _ => (mul_one 1).symm) (fun _ _ _ => rfl) contDiffOn_const (fun _ _ => norm_one)
    (fun β hβ _ => hXne _ (by simpa using hβ))
  refine ⟨Z, hZd, fun s hs => ?_⟩
  rw [hZ s hs, _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X hXbot (hXne ⊤ top_ne_bot) hXmul
    (fun I => by by_cases hI : I = ⊥ <;> simp [X, hI]) s hs]
  have h1 : ∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = 1 := fun P => hXne _ P.ne_bot
  simp only [h1]

end GlobalTheory
