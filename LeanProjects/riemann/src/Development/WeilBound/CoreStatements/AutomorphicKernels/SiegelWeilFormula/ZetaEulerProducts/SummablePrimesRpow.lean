import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DedekindZetaEulerProductMulSubOneEntireNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneSubRePosOfNormLeHalf

open NumberField IsDedekindDomain

namespace PositivityTheory.Lord

theorem dedekindZeta_eq_exp (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  classical
  set X : Ideal (𝓞 K) → ℂ := fun I => if I = ⊥ then 0 else 1 with hX
  have h0 : X ⊥ = 0 := by simp [hX]
  have h1 : ∀ I, I ≠ ⊥ → X I = 1 := fun I hI => by simp only [hX, if_neg hI]
  have hmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    by_cases hI : I = ⊥
    · subst hI
      rw [Ideal.bot_mul, h0, zero_mul]
    by_cases hJ : J = ⊥
    · subst hJ
      rw [Ideal.mul_bot, h0, mul_zero]
    rw [h1 I hI, h1 J hJ, h1 _ (fun h => (Ideal.mul_eq_bot.1 h).elim hI hJ), one_mul]
  have hle : ∀ I, ‖X I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · subst hI
      rw [h0]; simp
    · rw [h1 I hI]; simp
  have h := GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X h0 (h1 _ top_ne_bot) hmul hle s hs
  have hs0 : -s ≠ 0 := by
    rintro h0
    rw [neg_eq_zero] at h0
    subst h0
    norm_num at hs
  have e1 : ∀ I : Ideal (𝓞 K), X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) =
      ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) := by
    intro I
    by_cases hI : I = ⊥
    · subst hI
      rw [h0, zero_mul, Ideal.absNorm_bot, Nat.cast_zero, Complex.zero_cpow hs0]
    · rw [h1 I hI, one_mul]
  have e2 : ∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = 1 := fun P => h1 _ P.ne_bot
  simp only [e1, e2] at h
  rw [GlobalTheory.Mem.ZetaPole.dedekindZeta_eq_tsum_ideal K hs, h]

theorem two_le_absNorm' (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h =>
    P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem summable_primes_rpow (K : Type) [Field K] [NumberField K] (σ : ℝ) (hσ : 1 < σ) :
    Summable fun P : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-σ) := by
  have h := GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (σ : ℂ)) (by simpa using hσ)
  have hinj : Function.Injective fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal :=
    fun P Q hPQ => HeightOneSpectrum.ext hPQ
  refine (h.comp_injective hinj).congr fun P => ?_
  have hpos : 0 < Ideal.absNorm P.asIdeal := by have := two_le_absNorm' K P; omega
  simp only [Function.comp_apply]
  rw [Complex.norm_natCast_cpow_of_pos hpos]
  simp

theorem zeta_euler (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) => 1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))
        (GroundTheory.Global.continuedDedekindZeta K s)⁻¹ ∧
      GroundTheory.Global.continuedDedekindZeta K s ≠ 0 := by
  have hE := ((GlobalTheory.eulerProduct_eq_exp_and_pos (HeightOneSpectrum (𝓞 K))
    (fun P => Ideal.absNorm P.asIdeal) (fun _ => 1) (two_le_absNorm' K) (fun _ => by simp)
    (summable_primes_rpow K)).1 s hs).2
  rw [← dedekindZeta_eq_exp K hs, ← GroundTheory.Global.continuedDedekindZeta_eq K hs] at hE
  have hne : GroundTheory.Global.continuedDedekindZeta K s ≠ 0 := by
    rw [GroundTheory.Global.continuedDedekindZeta_eq K hs, dedekindZeta_eq_exp K hs]
    exact Complex.exp_ne_zero _
  refine ⟨?_, hne⟩
  have := hE.inv₀ hne
  simpa using this

end PositivityTheory.Lord
