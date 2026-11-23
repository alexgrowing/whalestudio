import Mathlib
import GroundTheory.GlobalFields.Artin.Series
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField Polynomial

namespace GroundTheory.Global

section Det

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

end Det

variable {K L V : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [IsGalois K L] in
theorem norm_absNorm_cpow_neg_lt_one (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 :=
  ((norm_absNorm_cpow_neg_le v le_rfl).trans (absNorm_rpow_neg_le_half v hs.le)).trans_lt
    (by norm_num)

theorem artinL_one {s : ℂ} (hs : 1 < s.re) :
    artinL K L (1 : Gal(L/K) → ℂ) s = dedekindZeta K s := by
  have hx := fun v : HeightOneSpectrum (𝓞 K) => norm_absNorm_cpow_neg_lt_one v hs
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), 1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) ≠ 0 :=
    fun v h => by
      have h1 := hx v
      rw [← sub_eq_zero.1 h, norm_one] at h1
      exact lt_irrefl _ h1
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), artinLocalLog K L (1 : Gal(L/K) → ℂ) s v =
      -Complex.log (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := fun v => by
    rw [artinLocalLog]
    simp only [artinTerm, localAverage_one, one_mul]
    exact (Complex.hasSum_taylorSeries_neg_log (hx v)).tsum_eq
  have h1 : HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (artinL K L (1 : Gal(L/K) → ℂ) s) := by
    rw [artinL]
    convert (hasSum_artinLocalLog_artinLogL (1 : Gal(L/K) → ℂ) hs).cexp using 1
    funext v
    rw [Function.comp_apply, hloc, Complex.exp_neg, Complex.exp_log (hne v)]
  have h2 : HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (dedekindZeta K s) := by
    rw [← HeckeCharacter.LFunction_one]
    convert (1 : HeckeCharacter K).LFunction_hasProd_all hs using 3 with v
    rw [HeckeCharacter.coeff_one v.ne_bot, one_mul]
  exact h1.unique h2

end GroundTheory.Global
