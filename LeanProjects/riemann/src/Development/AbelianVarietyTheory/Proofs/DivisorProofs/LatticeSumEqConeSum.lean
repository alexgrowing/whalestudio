import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualSignedPositiveConeIffTotallyPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzConstantInverseDifferentEisensteinStatement
open NumberField
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.EisPerB
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

theorem latM_ne_zero (𝔞 : Frac F) : latM 𝔞 ≠ 0 := by
  rw [latM_eq_dual]
  exact FractionalIdeal.dual_ne_zero ℤ ℚ 𝔞.ne_zero

theorem nrm_pos (𝔞 : Frac F) : 0 < nrm 𝔞 := by
  unfold nrm
  have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm

theorem eisTerm_eq [IsTotallyReal F] (k : ℕ) (z : Emb F → ℂ) (a b : F) :
    eisTerm k 0 z (a, b) = ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
      lhsTerm k (fun τ => ((τ b : ℝ) : ℂ) * z τ) a := by
  have hprod : ∏ τ, latPt z (a, b) τ = (2 * (Real.pi : ℂ) * Complex.I) ^ (Module.finrank ℚ F) *
      ∏ τ : F →+* ℝ, (((τ b : ℝ) : ℂ) * z τ + ((τ a : ℝ) : ℂ)) := by
    rw [← card_realEmb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [latPt]; ring
  unfold eisTerm lhsTerm
  rw [hprod]
  simp only [mul_zero, Complex.cpow_zero, mul_one, zpow_neg, zpow_natCast]
  ring

theorem rhsTerm_eq [IsTotallyReal F] (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (ν b : F) :
    rhsTerm k (fun τ => ((τ b : ℝ) : ℂ) * z τ) ν = (nrm 𝔞 : ℂ) ^ (k - 1) * qTerm 𝔞 k z (ν, b) := by
  have hN : ∏ τ : F →+* ℝ, τ ν = ((Algebra.norm ℚ ν : ℚ) : ℝ) := by
    have h := prod_emb ν
    rw [← Complex.ofReal_prod] at h
    exact_mod_cast h
  have hpos := nrm_pos 𝔞
  have hreal : |((Algebra.norm ℚ ν : ℚ) : ℝ)| ^ (k - 1) =
      nrm 𝔞 ^ (k - 1) * (|((Algebra.norm ℚ ν : ℚ) : ℝ)| / nrm 𝔞) ^ (k - 1) := by
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hpos.ne')]
  have hsum : ∑ τ : F →+* ℝ, ((τ ν : ℝ) : ℂ) * (((τ b : ℝ) : ℂ) * z τ) =
      ∑ τ : F →+* ℝ, ((τ (ν * b) : ℝ) : ℂ) * z τ := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, Complex.ofReal_mul, mul_assoc]
  unfold rhsTerm qTerm qPow
  rw [hN, hsum, hreal, Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc]

end GlobalTheory.EisPerB

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent in

theorem GlobalTheory.EisPerB.lattice_sum_eq_cone_sum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
    ∀ (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k → ∀ (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
      Summable (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (ν.1, b)) ∧
      HasSum (fun a : (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F) => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k 0 z ((a : F), b))
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) *
          ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (ν.1, b)) := by
  intro F _ _ _ hLip 𝔞 k hk2 hke b hb z hz
  have hz'im : ∀ τ, ((fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) τ).im ≠ 0 := by
    intro τ
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  obtain ⟨hL, hR, hEq⟩ := hLip F (latM 𝔞) (GlobalTheory.EisPerB.latM_ne_zero 𝔞) k hk2 hke _ hz'im
  let e : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ≃ GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b :=
    Equiv.subtypeEquivRight (fun ν => GlobalTheory.T.mem_traceDualSignedPositiveCone_iff_totallyPositive F 𝔞 b hb z hz ν)
  have hN : (nrm 𝔞 : ℂ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (GlobalTheory.EisPerB.nrm_pos 𝔞).ne')
  have hRq : ∀ ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ),
      rhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ν = (nrm 𝔞 : ℂ) ^ (k - 1) * qTerm 𝔞 k z ((e ν).1, b) :=
    fun ν => GlobalTheory.EisPerB.rhsTerm_eq 𝔞 k z ν.1 b
  have hsumQ : Summable (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => qTerm 𝔞 k z (ν.1, b)) := by
    have h1 : Summable (fun ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) =>
        qTerm 𝔞 k z ((e ν).1, b)) := by
      refine (hR.mul_left ((nrm 𝔞 : ℂ) ^ (k - 1))⁻¹).congr fun ν => ?_
      rw [hRq, inv_mul_cancel_left₀ hN]
    exact e.summable_iff.1 h1
  have htsum : ∑' ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ),
      rhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ν =
      (nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b) := by
    rw [tsum_congr hRq, tsum_mul_left]
    congr 1
    exact e.tsum_eq (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => qTerm 𝔞 k z (ν.1, b))
  refine ⟨hsumQ, ?_⟩
  have hE : (fun a : (latM 𝔞 : Set F) => eisTerm k 0 z ((a : F), b)) = fun a : (latM 𝔞 : Set F) =>
      ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
        lhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) a :=
    funext fun a => GlobalTheory.EisPerB.eisTerm_eq k z a b
  rw [hE]
  have h := hL.hasSum.mul_left ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹
  rw [hEq, htsum] at h
  rw [← GlobalTheory.T.lipschitzConstant_inverseDifferent_eisenstein F 𝔞 k (by omega)]
  have hv : ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ * lipConst k (latM 𝔞) *
      (nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b) =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
      (lipConst k (latM 𝔞) * ((nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b))) := by
    ring
  rw [hv]
  exact h
