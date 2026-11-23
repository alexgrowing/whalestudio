import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

namespace GlobalTheory.UnrEuler

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def conjO (σ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)

theorem conjO_le (σ : E →ₐ[F] E) : (𝓞 E)⁰ ≤ Submonoid.comap (conjO σ) (𝓞 E)⁰ := by
  intro x hx
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at *
  intro h
  apply hx
  have h' : σ (x : E) = 0 := by
    simpa [conjO, RingOfIntegers.mapRingHom_apply] using congrArg (fun y : 𝓞 E => (y : E)) h
  exact RingOfIntegers.coe_eq_zero_iff.1 ((map_eq_zero_iff σ σ.toRingHom.injective).1 h')

def conjI (σ : E →ₐ[F] E) (𝔠 : FractionalIdeal (𝓞 E)⁰ E) : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.extended E (conjO_le σ) 𝔠

variable (E) in

def diffE : FractionalIdeal (𝓞 E)⁰ E := ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)

def idA (σ : E →ₐ[F] E) (𝔟 𝔠 : FractionalIdeal (𝓞 E)⁰ E) : FractionalIdeal (𝓞 E)⁰ E :=
  𝔟 * (conjI σ 𝔠)⁻¹ * (diffE E)⁻¹

def nrm (𝔞 : FractionalIdeal (𝓞 E)⁰ E) : ℝ := ((FractionalIdeal.absNorm 𝔞 : ℚ) : ℝ)

def unrFac (ν : Chr F E) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (s : ℂ) (v : Pl F) : ℂ :=
  (∏ w ∈ aboveF (L := E) F v, ((val ν w ^ FractionalIdeal.count E w 𝔞 : ℂˣ) : ℂ) *
    npow w (-(s * (FractionalIdeal.count E w 𝔞 : ℂ)))) * Lv (charFam ν) v s

variable (F) in

def kaOne (a a' : ℕ) (𝔟 𝔠 : FractionalIdeal (𝓞 E)⁰ E) : ℝ :=
  (nrm 𝔠 * |(discr F : ℝ)|) ^ (-(a : ℝ) / 2) * nrm 𝔟 ^ (-(((a + a' : ℕ) : ℝ) - 2) / 2)

variable (F) in

def kaZero (a' : ℕ) (𝔠 : FractionalIdeal (𝓞 E)⁰ E) : ℝ := (nrm 𝔠 * |(discr F : ℝ)|) ^ (-(a' : ℝ) / 2)

theorem nrm_pos {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h : 𝔞 ≠ 0) : 0 < nrm 𝔞 := by
  unfold nrm
  have := FractionalIdeal.absNorm_nonneg 𝔞
  have h2 : FractionalIdeal.absNorm 𝔞 ≠ 0 := by
    rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact_mod_cast lt_of_le_of_ne this (Ne.symm h2)

theorem locChar_eq_val_zpow {ν : Chr F E} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt ν w)
    {b : (w.adicCompletion E)ˣ} {k : ℤ} (hb : Valued.v (b : w.adicCompletion E) = WithZero.exp (-k)) :
    locChar ν w b = val ν w ^ k := by
  have hϖ := Formalism.L2.Host.unif_spec w
  unfold Formalism.L2.Host.IsUnifAt at hϖ
  set ϖ := Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)
  have hu : Formalism.L2.Host.IsUnitAt w (b * ϖ⁻¹ ^ k) := by
    unfold Formalism.L2.Host.IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_inv_eq_inv_val, map_inv₀, hb, hϖ,
      ← WithZero.exp_neg, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have h1 := h _ hu
  rw [map_mul, map_zpow, map_inv] at h1
  have h2 : val ν w = locChar ν w ϖ := rfl
  rw [h2]
  rw [inv_zpow, mul_inv_eq_one] at h1
  exact h1

theorem conjI_ne_zero (σ : E →ₐ[F] E) {𝔠 : FractionalIdeal (𝓞 E)⁰ E} (h : 𝔠 ≠ 0) : conjI σ 𝔠 ≠ 0 := by
  refine FractionalIdeal.extended_ne_zero E (conjO_le σ) ?_ h (zero_notMem_nonZeroDivisors)
  intro x y hxy
  apply RingOfIntegers.ext
  have : σ (x : E) = σ (y : E) := by
    simpa [conjO, RingOfIntegers.mapRingHom_apply] using congrArg (fun z : 𝓞 E => (z : E)) hxy
  exact σ.toRingHom.injective this

theorem diffE_ne_zero : diffE E ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

theorem nu_triv (B : Base F E) {a a' : ℕ} (X : Chars F E) (hX : X.IsGood B a a') (he : Even (a + a')) (x : (AF F)ˣ) :
    X.ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1 := by
  have hα := hX.resα x
  have hβ := hX.resβ x
  have hp : ((-1 : ℂ)) ^ a' = (-1) ^ a := by
    have h1 : ((-1 : ℂ)) ^ a * (-1) ^ a' = 1 := by rw [← pow_add, he.neg_one_pow]
    have h2 : ((-1 : ℂ)) ^ a * (-1) ^ a = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) (h1.trans h2.symm)
  rw [Chars.ν, MonoidHom.div_apply, div_eq_one]
  apply Circle.coe_injective
  rw [hα, hβ]
  split_ifs
  · rfl
  · exact hp

theorem idealVal_mul (ν : Chr F E) {I J : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealVal ν (I * J) = idealVal ν I * idealVal ν J := by
  unfold idealVal
  simp_rw [FractionalIdeal.count_mul E _ hI hJ, zpow_add]
  apply finprod_mul_distrib
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset fun w hw => ?_
    intro h0
    exact hw (by simp [h0])
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors J)).subset fun w hw => ?_
    intro h0
    exact hw (by simp [h0])

theorem idealVal_inv (ν : Chr F E) (I : FractionalIdeal (𝓞 E)⁰ E) : idealVal ν I⁻¹ = (idealVal ν I)⁻¹ := by
  unfold idealVal
  simp_rw [FractionalIdeal.count_inv, zpow_neg]
  exact finprod_inv_distrib _

end GlobalTheory.UnrEuler
