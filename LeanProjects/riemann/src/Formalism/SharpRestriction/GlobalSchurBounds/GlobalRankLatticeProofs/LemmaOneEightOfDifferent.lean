import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PointsPropertyOfD7
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightOfPolarisation

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal
open scoped Pointwise
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices Formalism.FrobeniusOrbits.OrdUnimod

def DiffK (D : D7) : Prop :=
  ∃ β : 𝓞 D.host.E, (β : D.host.E) = D.host.sqrtMinusD ∧
    (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = Ideal.span {β}

def NormK (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ →
    Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc *
      (D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc) =
    Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 D.host.E)}

namespace PolarisationData

variable (D : D7)

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

theorem galE_conj : D.host.galE D.host.conj = D.R.cc := by
  show D.host.gal (D.host.gal.symm _) = _
  exact MulEquiv.apply_symm_apply _ _

theorem conj_b : D.host.conj D.host.sqrtMinusD = - D.host.sqrtMinusD := by
  show D.host.conj D.host.sqd = - D.host.sqd
  rw [D.host.gal_sqd, show D.host.gal D.host.conj = D.R.cc from galE_conj D]
  simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]

private theorem smul_ne_bot' (σ : D.host.E ≃ₐ[ℚ] D.host.E) (I : Ideal (𝓞 D.host.E)) (hI : I ≠ ⊥) :
    σ • I ≠ ⊥ := by
  intro h
  apply hI
  have k : σ⁻¹ • σ • I = I := inv_smul_smul σ I
  rw [← k, h]
  first
    | simp
    | (rw [Ideal.pointwise_smul_def]; exact Ideal.map_bot)

theorem sqrt_d_pos : 0 < Real.sqrt D.host.d := by
  exact Real.sqrt_pos.mpr (by exact_mod_cast D.host.hyp.2.1.pos)

theorem b_ne_zero : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have k := D.host.sqd_sq
  have hd : (D.host.d : D.host.E) ≠ 0 := by exact_mod_cast D.host.hyp.2.1.ne_zero
  rw [show D.host.sqd = D.host.sqrtMinusD from rfl, h] at k
  apply hd
  linear_combination k

theorem mem_coe_smul (σ : D.host.E ≃ₐ[ℚ] D.host.E) (A : Ideal (𝓞 D.host.E)) (z : D.host.E) :
    σ z ∈ ((σ • A : Ideal (𝓞 D.host.E)) : FI) ↔ z ∈ (A : FI) := by
  simp only [FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨a, ha, hz⟩
    refine ⟨σ⁻¹ • a, (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 ha, ?_⟩
    have e1 : algebraMap (𝓞 D.host.E) D.host.E (σ⁻¹ • a) =
        σ⁻¹ (algebraMap (𝓞 D.host.E) D.host.E a) := rfl
    rw [e1, hz]
    simp
  · rintro ⟨a, ha, rfl⟩
    exact ⟨σ • a, Ideal.smul_mem_pointwise_smul σ a A ha, rfl⟩

theorem mem_quot_smul (σ : D.host.E ≃ₐ[ℚ] D.host.E) (A Bd : Ideal (𝓞 D.host.E)) (hB : Bd ≠ ⊥)
    (x : D.host.E) :
    σ x ∈ ((σ • A : Ideal (𝓞 D.host.E)) : FI) * ((σ • Bd : Ideal (𝓞 D.host.E)) : FI)⁻¹ ↔
      x ∈ (A : FI) * (Bd : FI)⁻¹ := by
  have hB0 : ((Bd : Ideal (𝓞 D.host.E)) : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hB
  have hB1 : ((σ • Bd : Ideal (𝓞 D.host.E)) : FI) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (smul_ne_bot' D σ Bd hB)
  rw [← div_eq_mul_inv, ← div_eq_mul_inv]
  first
    | rw [FractionalIdeal.mem_div_iff_of_ne_zero hB0, FractionalIdeal.mem_div_iff_of_ne_zero hB1]
    | rw [FractionalIdeal.mem_div_iff_of_nonzero hB0, FractionalIdeal.mem_div_iff_of_nonzero hB1]
  constructor
  · intro h y hy
    have k := h (σ y) ((mem_coe_smul D σ Bd y).2 hy)
    rw [← map_mul] at k
    exact (mem_coe_smul D σ A (x * y)).1 k
  · intro h y hy
    have hy' : σ (σ.symm y) ∈ ((σ • Bd : Ideal (𝓞 D.host.E)) : FI) := by
      rw [AlgEquiv.apply_symm_apply]; exact hy
    have k := (mem_coe_smul D σ A _).2 (h _ ((mem_coe_smul D σ Bd _).1 hy'))
    rw [map_mul, AlgEquiv.apply_symm_apply] at k
    exact k

theorem spanSingleton_neg_one :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (-1 : D.host.E) = 1 := by
  ext z
  rw [FractionalIdeal.mem_spanSingleton, FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨-a, by simp [Algebra.smul_def]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨-a, by simp [Algebra.smul_def]⟩

theorem diffEK : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) =
    D.host.𝔟 * (D.host.conj • D.host.𝔟) := by
  exact D.host.𝔟_spec.1

attribute [local instance] FractionRing.liftAlgebra in
theorem diffE : differentIdeal ℤ (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) *
    (differentIdeal ℤ (𝓞 D.host.K)).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  exact differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ _ _

theorem im_pos (N : ℕ) (hN : N ≠ 0) (φ : D.host.E →+* ℂ) (hφ : φ ∈ PhiEmb D) :
    0 < (φ (-1 / ((N : D.host.E) * D.host.sqrtMinusD))).im := by
  have hs : φ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
    (SlopeTestRemainingChoices.mem_PhiEmb_iff D φ).1 hφ
  have hpos := sqrt_d_pos D
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, hs]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hs0 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have key : (-1 : ℂ) / ((N : ℂ) * (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))) =
      Complex.I * ((((N : ℝ) * Real.sqrt D.host.d)⁻¹ : ℝ) : ℂ) := by
    rw [div_eq_iff (mul_ne_zero hN' (mul_ne_zero Complex.I_ne_zero hs0))]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
  rw [key]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, add_zero, mul_zero, zero_add]
  exact inv_pos.mpr (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hN) hpos)

theorem pol (hA : DiffK D) (hB : NormK D) : PolPart D := by
  intro cc hcc
  obtain ⟨β, hβ, hβspan⟩ := hA
  have hN0 : Ideal.absNorm cc ≠ 0 := fun h => hcc (Ideal.absNorm_eq_zero_iff.mp h)
  have hNE : ((Ideal.absNorm cc : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hN0
  have hb0 := b_ne_zero D
  have hNcc := hB cc hcc

  have hb𝔟 : D.host.𝔟 ≠ ⊥ := by
    intro h
    have k := D.host.𝔟_spec.2
    rw [h] at k
    simp at k
  have hAbot : Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc ≠ ⊥ := by
    intro h
    rw [h, bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hNcc
    exact hN0 (by exact_mod_cast hNcc)
  refine ⟨-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD), ?_, ?_,
    fun φ hφ => im_pos D (Ideal.absNorm cc) hN0 φ hφ, ?_⟩
  · have hs : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ D.host.sqd
    exact div_mem (neg_mem (one_mem _)) (mul_mem (natCast_mem _ _) hs)
  · rw [map_div₀, map_neg, map_one, map_mul, map_natCast, conj_b, mul_neg, div_neg]
  · intro y

    have hprod : ((differentIdeal ℤ (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) : FI) *
        (FractionalIdeal.spanSingleton _ (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD)) *
          (((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
            ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹)) *
        (((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
          (D.host.𝔟 : FI)⁻¹) = 1 := by
      have h1 : (D.host.𝔟 : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hb𝔟
      have h2 : ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI) ≠ 0 :=
        FractionalIdeal.coeIdeal_ne_zero.mpr (smul_ne_bot' D _ _ hb𝔟)
      have hN2 : ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
          ((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) =
          FractionalIdeal.spanSingleton _ ((Ideal.absNorm cc : ℕ) : D.host.E) := by
        rw [← FractionalIdeal.coeIdeal_mul, hNcc, FractionalIdeal.coeIdeal_span_singleton, map_natCast]
      have hsp : ((Ideal.span {β} : Ideal (𝓞 D.host.E)) : FI) =
          FractionalIdeal.spanSingleton _ D.host.sqrtMinusD := by
        rw [FractionalIdeal.coeIdeal_span_singleton]
        congr 1
      rw [diffE, diffEK, hβspan, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, hsp]
      calc _ = ((D.host.𝔟 : FI) * (D.host.𝔟 : FI)⁻¹) *
            (((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI) *
              ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹) *
            ((((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
              ((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI)) *
            (FractionalIdeal.spanSingleton _ D.host.sqrtMinusD *
              FractionalIdeal.spanSingleton _
                (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD)))) := by ring
        _ = 1 := by
          rw [mul_inv_cancel₀ h1, mul_inv_cancel₀ h2, hN2, FractionalIdeal.spanSingleton_mul_spanSingleton,
            FractionalIdeal.spanSingleton_mul_spanSingleton, one_mul, one_mul]
          have e : ((Ideal.absNorm cc : ℕ) : D.host.E) * (D.host.sqrtMinusD *
              (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD))) = -1 := by
            field_simp
          rw [e, spanSingleton_neg_one]
    have hM0 : FractionalIdeal.spanSingleton _ (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD)) *
          (((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
            ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹) ≠ 0 := by
      intro h
      rw [h, mul_zero, zero_mul] at hprod
      exact zero_ne_one hprod

    have hdual : FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton _
          (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD)) *
          (((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
            ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹)) =
        ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
          (D.host.𝔟 : FI)⁻¹ := by
      rw [FractionalIdeal.dual_eq_mul_inv ℤ ℚ, ← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FI)),
        ← coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E), ← mul_inv]
      exact inv_eq_of_mul_eq_one_right hprod
    show y ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
          (D.host.𝔟 : FI)⁻¹ ↔ ∀ x ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
          (D.host.𝔟 : FI)⁻¹, _
    conv_lhs => rw [← hdual]
    rw [FractionalIdeal.mem_dual hM0]
    constructor
    · intro h x hx
      have hw := (mem_quot_smul D D.host.conj _ _ hb𝔟 x).2 hx
      have k := h _ (FractionalIdeal.mem_singleton_mul.2 ⟨_, hw, rfl⟩)
      rw [Algebra.traceForm_apply] at k
      rw [show -1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * D.host.conj x * y =
        y * (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * D.host.conj x) by ring]
      exact k
    · intro h u hu
      obtain ⟨w, hw, hweq⟩ := FractionalIdeal.mem_singleton_mul.1 hu
      have hw' : D.host.conj (D.host.conj.symm w) ∈
          ((D.host.conj • Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) : FI) *
            ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FI)⁻¹ := by
        rw [AlgEquiv.apply_symm_apply]; exact hw
      have k := h _ ((mem_quot_smul D D.host.conj _ _ hb𝔟 _).1 hw')
      rw [AlgEquiv.apply_symm_apply] at k
      rw [Algebra.traceForm_apply]
      first
        | (rw [← hweq]; rw [show y * (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w) =
            -1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w * y by ring]; exact k)
        | (rw [hweq]; rw [show y * (-1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w) =
            -1 / (((Ideal.absNorm cc : ℕ) : D.host.E) * D.host.sqrtMinusD) * w * y by ring]; exact k)

end PolarisationData

theorem lemma_one_eight_of_different (D : D7) (hA : DiffK D) (hB : NormK D) : Conclusion8 D := by
  exact lemma_one_eight_of_polarisation D (PolarisationData.pol D hA hB)

end Formalism.MainNotions.UnusedSlot33

end
