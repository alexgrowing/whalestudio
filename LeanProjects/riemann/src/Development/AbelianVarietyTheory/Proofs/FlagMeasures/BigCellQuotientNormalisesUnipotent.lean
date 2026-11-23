import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.FormalDegreeBessel.FinalBF
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.BigConvLevi

open Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.BigCellHermitian

variable {k r : ℕ}

theorem hb_mul_self : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

theorem isUnit_det_of_hb {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : μᴴ * Hb k * μ = Hb k) :
    IsUnit μ.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hb k * μᴴ * Hb k)
  calc Hb k * μᴴ * Hb k * μ = Hb k * (μᴴ * Hb k * μ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hb_mul_self]

theorem conj_mem_of_levi (A B n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hAB : A * B = 1) (hA : A ∈ UH (Hpk k r)) (hB : B ∈ UH (Hpk k r))
    (hA1 : ∀ i j, ¬ mid k r j → A i j = if i = j then 1 else 0)
    (hB1 : ∀ i j, ¬ mid k r j → B i j = if i = j then 1 else 0)
    (hB3 : ∀ m j, mid k r j → ¬ mid k r m → B m j = 0)
    (hn : n ∈ Nset k r) : A * n * B ∈ Nset k r := by
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hA hn.1) hB, ?_, ?_⟩
  · intro a i hai
    have hea : ¬ mid k r (eI k r a) := by
      have := a.isLt; simp only [mid, eI]; omega
    rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
    · rw [hB1 _ _ hea, if_pos rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
      · rw [hn.2.1 a (eI k r a) (by simp [eI]), if_pos rfl, mul_one, hA1 _ _ hea]
      · intro l _ hl
        by_cases hla : a.val ≤ l.val
        · rw [hn.2.1 a l hla, if_neg hl, mul_zero]
        · have hlm : ¬ mid k r l := by have := a.isLt; simp only [mid]; omega
          rw [hA1 i l hlm, if_neg (by rw [Fin.ext_iff]; omega), zero_mul]
      · simp
    · intro l _ hl
      rw [hB1 _ _ hea, if_neg hl, mul_zero]
    · simp
  · intro i j hj1 hj2 hi
    have hjm : mid k r j := ⟨hj1, hj2⟩
    rw [Matrix.mul_apply]
    have key : ∀ m, (A * n) i m * B m j = A i m * B m j := by
      intro m
      by_cases hm : mid k r m
      · congr 1
        rw [Matrix.mul_apply, Finset.sum_eq_single m]
        · rw [hn.2.2 m m hm.1 hm.2 hm.1, if_pos rfl, mul_one]
        · intro l _ hl
          by_cases hlr : r ≤ l.val
          · rw [hn.2.2 l m hm.1 hm.2 hlr, if_neg hl, mul_zero]
          · have hlm : ¬ mid k r l := by simp only [mid]; omega
            rw [hA1 i l hlm, if_neg (by rw [Fin.ext_iff]; omega), zero_mul]
        · simp
      · rw [hB3 m j hjm hm, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl (fun m _ => key m), ← Matrix.mul_apply, hAB, Matrix.one_apply]

theorem cellQuot_props (c : Fin r → ℂ) (μ₁ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hc : ∀ a, c a ≠ 0) (h₁ : μ₁ᴴ * Hb k * μ₁ = Hb k) (h : μᴴ * Hb k * μ = Hb k) :
    (bigCell k r c μ₁)⁻¹ * bigCell k r c μ ∈ UH (Hpk k r) ∧
    (∀ i j, ¬ mid k r j → ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) i j = if i = j then 1 else 0) ∧
    (∀ m j, mid k r j → ¬ mid k r m → ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) m j = 0) := by
  have hg₁ := big_cell_mem_holds k r c μ₁ hc h₁
  have hg := big_cell_mem_holds k r c μ hc h
  have u₁ := WeylGroupFacts.isUnit_of_uh hg₁
  have hμ₁ := isUnit_det_of_hb h₁
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hg₁) hg, ?_, ?_⟩
  · intro i j hj
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun l _ => by rw [bc_out_col c μ μ₁ l j hj]),
      ← Matrix.mul_apply, Matrix.nonsing_inv_mul _ u₁, Matrix.one_apply]
  · intro m j hj hm
    obtain ⟨t, rfl⟩ := mid_exists hj
    have e1 : (Pi.single (wI k r t) 1 : Fin (2 * r + k + 1) → ℂ) = jV k r (Pi.single t 1) := by
      funext i
      by_cases hi : mid k r i
      · obtain ⟨s, rfl⟩ := mid_exists hi
        rw [jV_wI]
        simp only [Pi.single_apply, wI_inj.eq_iff]
      · rw [jV_out _ hi, Pi.single_apply, if_neg (fun he : i = wI k r t => hi (he ▸ mid_wI t))]
    have col : ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) m (wI k r t) =
        (((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) *ᵥ Pi.single (wI k r t) 1) m := by
      rw [Matrix.mulVec_single_one]; rfl
    have back : ∀ v : Fin (k + 1) → ℂ,
        jV k r v = bigCell k r c μ₁ *ᵥ jV k r (μ₁⁻¹ *ᵥ v) := by
      intro v
      rw [bigCell_mulVec_jV, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hμ₁, Matrix.one_mulVec]
    rw [col, ← Matrix.mulVec_mulVec, e1, bigCell_mulVec_jV, back, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ u₁, Matrix.one_mulVec, jV_out _ hm]

theorem levi_conj_mem_iff : ∀ (k r : ℕ) (c : Fin r → ℂ) (μ₁ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    (∀ a, c a ≠ 0) → μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k →
    μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k →
    ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, n ∈ Formalism.QuantumDeterminants.Nset k r ↔
      (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ * n *
        ((Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro k r c μ₁ μ hc h₁ h n
  have u₁ := WeylGroupFacts.isUnit_of_uh (big_cell_mem_holds k r c μ₁ hc h₁)
  have u := WeylGroupFacts.isUnit_of_uh (big_cell_mem_holds k r c μ hc h)
  obtain ⟨hA, hA1, hA3⟩ := cellQuot_props c μ₁ μ hc h₁ h
  obtain ⟨hB, hB1, hB3⟩ := cellQuot_props c μ μ₁ hc h h₁
  have hinv : ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)⁻¹ = (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ u₁]
  have hAB : (bigCell k r c μ₁)⁻¹ * bigCell k r c μ * ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u, Matrix.nonsing_inv_mul _ u₁]
  have hBA : (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u₁, Matrix.nonsing_inv_mul _ u]
  rw [hinv]
  constructor
  · exact conj_mem_of_levi _ _ n hAB hA hB hA1 hB1 hB3
  · intro hn'
    have := conj_mem_of_levi _ _ _ hBA hB hA hB1 hA1 hA3 hn'
    have e : (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ *
        ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ * n * ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁)) *
        ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) = n := by
      calc _ = ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)) * n *
            ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)) := by
            simp only [Matrix.mul_assoc]
        _ = n := by rw [hBA, Matrix.one_mul, Matrix.mul_one]
    rwa [e] at this

end GlobalTheory.BigConvLevi
