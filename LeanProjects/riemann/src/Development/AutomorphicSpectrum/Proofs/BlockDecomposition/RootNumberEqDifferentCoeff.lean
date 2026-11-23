import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation

set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors NNReal

namespace GlobalTheory.CompanionTheory.PartialZeta

noncomputable section

variable {F : Type} [Field F] [NumberField F] {χ : HeckeCharacter F}

theorem conductor_eq_top (h : standardOpenSubgroup F ≤ χ.toIdele.ker) : χ.conductor = ⊤ := by
  have hd : χ.conductor ∣ ⊤ := by
    refine (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine h ((mem_standardOpenSubgroup_iff_toFinite_mem _).2 ?_)
    rw [toFinite_ofFinite]
    have hx' : x ∈ idealLevel (⊤ : Ideal (𝓞 F)) := hx
    rw [idealLevel, mem_finiteLevel] at hx'
    rw [mem_finiteLevel]
    intro v
    have hv := hx' v
    have h0 : multiplicity v.asIdeal (⊤ : Ideal (𝓞 F)) = 0 :=
      multiplicity_eq_zero.2 fun hdv ↦ v.isPrime.ne_top (by
        rwa [Ideal.dvd_iff_le, top_le_iff] at hdv)
    rw [h0] at hv
    exact hv
  rwa [Ideal.dvd_iff_le, top_le_iff] at hd

theorem infiniteWeight_eq_zero (h : standardOpenSubgroup F ≤ χ.toIdele.ker)
    (w : InfinitePlace F) : χ.infiniteWeight w = 0 := by
  have hp : χ.infiniteParams w = (0, 0) := by
    refine (χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
    have h1 : χ.infiniteComponent w a = 1 := h (infiniteEmbedding_mem_standardOpenSubgroup w a)
    simp [h1]
  rw [HeckeCharacter.infiniteWeight, hp]

theorem idealUnit_eq_one {I : Ideal (𝓞 F)} (hI : I = ⊤) (h : I ≠ ⊥) : idealUnit I h = 1 := by
  subst hI
  ext
  simp [idealUnit]

theorem finiteFourier_eq (h : χ.conductor = ⊤) {δ : (FiniteAdeleRing (𝓞 F) F)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    finiteFourier F χ.finiteTestFun ((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
      (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) := by
  have hE : IsEmpty χ.conductorPrimes := ⟨fun v ↦ by
    have hv := χ.mem_conductorPrimes.1 v.2
    rw [h, Ideal.dvd_iff_le, top_le_iff] at hv
    exact v.1.isPrime.ne_top hv⟩
  rw [χ.finiteFourier_finiteTestFun_inv_eq hδ, Finset.univ_eq_empty, Finset.prod_empty, mul_one]

theorem discr_sqrt_mul (h : χ.conductor = ⊤) :
    (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) * (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ) = 1 := by
  have hd : χ.discrNormConductor = |(discr F : ℝ)| := by
    rw [HeckeCharacter.discrNormConductor, h, Ideal.absNorm_top]
    simp
  have hpos : 0 < |(discr F : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F))
  have hs : ((NNReal.sqrt ‖discr F‖₊ : ℝ≥0) : ℝ) = Real.sqrt |(discr F : ℝ)| := by
    rw [Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  have hcp : ((|(discr F : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hpos.le]
    norm_num
  have hne : ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hpos).ne'
  have hinv : (((NNReal.sqrt ‖discr F‖₊)⁻¹ : ℝ≥0) : ℂ) = ((Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)⁻¹ := by
    rw [← hs]
    simp
  rw [hd, hcp, hinv, inv_mul_cancel₀ hne]

theorem rootNumber_eq_coeff_different (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F)
    (h : standardOpenSubgroup F ≤ χ.toIdele.ker) :
    χ.rootNumber = χ.coeff (differentIdeal ℤ (𝓞 F)) := by
  have hc := conductor_eq_top h
  have hδ := χ.toFractionalIdeal_conductorDifferentIdele
  have hcop : IsCoprime (differentIdeal ℤ (𝓞 F)) χ.conductor := by
    rw [hc, ← Ideal.one_eq_top]
    exact isCoprime_one_right
  have hmem : ofFinite χ.conductorDifferentIdele ∈ primeToLevel χ.conductor := by
    refine mem_primeToLevel.2 ⟨toInfinite_ofFinite _, fun v hv ↦ ?_⟩
    rw [hc, Ideal.dvd_iff_le, top_le_iff] at hv
    exact absurd hv v.isPrime.ne_top
  have hval : χ.coeff (differentIdeal ℤ (𝓞 F)) =
      (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) := by
    rw [χ.coeff_of_mem ⟨differentIdeal_ne_bot, hcop⟩]
    congr 1
    refine χ.idealCharacter_apply hmem _ ?_
    rw [hδ, idealUnit_eq_one hc, one_mul]
    rfl
  rw [hval, HeckeCharacter.rootNumber, HeckeCharacter.fourierConst, finiteFourier_eq hc hδ]
  simp only [infiniteWeight_eq_zero h, Int.natAbs_zero, pow_zero, Finset.prod_const_one, one_mul]
  linear_combination (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) * discr_sqrt_mul hc

end

end GlobalTheory.CompanionTheory.PartialZeta
