import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
open NumberField IsDedekindDomain

noncomputable section
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeIdealValue

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem finite_supp (χ : HChar L) (J : FractionalIdeal (𝓞 L)⁰ L) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v J).Finite := by
  refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors J)).subset fun v hv h => hv ?_
  simp [h]

theorem onId_mul (χ : HChar L) {a b : FractionalIdeal (𝓞 L)⁰ L} (ha : a ≠ 0) (hb : b ≠ 0) :
    χ.onId (a * b) = χ.onId a * χ.onId b := by
  unfold HChar.onId
  rw [← finprod_mul_distrib (finite_supp χ _) (finite_supp χ _)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul L v ha hb, zpow_add]

theorem onId_one (χ : HChar L) : χ.onId (1 : FractionalIdeal (𝓞 L)⁰ L) = 1 := by
  unfold HChar.onId
  simp [FractionalIdeal.count_one]

theorem onId_prime (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    χ.onId ((v.asIdeal : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := by
  unfold HChar.onId
  rw [finprod_eq_single _ v, FractionalIdeal.count_self, zpow_one]
  intro w hw
  rw [FractionalIdeal.count_maximal_coprime L w (Ne.symm hw), zpow_zero]

theorem inv_mem (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (O : Subring ℂ) (cc : Ideal (𝓞 L)) :
    cc ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 L), cc ≤ P.asIdeal →
      (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) →
    (((χ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : ℂˣ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm cc) : ℝ) : ℂ))⁻¹ ∈ O := by
  induction cc using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ I hI =>
    intro _ _
    have hI' : I = ⊤ := Ideal.isUnit_iff.1 hI
    subst hI'
    rw [FractionalIdeal.coeIdeal_top, onId_one, Ideal.absNorm_top]
    simp
  | h₃ I p hI hp ih =>
    intro _ hP
    let v : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hv := hP v Ideal.mul_le_left
    have hrest := ih hI fun P hle => hP P (le_trans Ideal.mul_le_right hle)
    rw [FractionalIdeal.coeIdeal_mul, onId_mul χ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero)
      (FractionalIdeal.coeIdeal_ne_zero.2 hI), map_mul, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), Units.val_mul, Complex.ofReal_mul]
    have e : χ.onId ((p : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := onId_prime χ v
    rw [e]
    have : (((χ.val v : ℂˣ) : ℂ) * (χ.onId (I : FractionalIdeal (𝓞 L)⁰ L) : ℂ) *
        (((Real.sqrt (Ideal.absNorm p) : ℝ) : ℂ) * ((Real.sqrt (Ideal.absNorm I) : ℝ) : ℂ)))⁻¹ =
        (((χ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ))⁻¹ *
        (((χ.onId (I : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm I) : ℝ) : ℂ))⁻¹ := by
      rw [← mul_inv]; congr 1; ring
    rw [this]
    exact O.mul_mem hv hrest

end GlobalTheory.HeckeIdealValue
