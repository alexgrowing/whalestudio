import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitalIntegralEqInvDegSmulStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.EllName

theorem rankOneInnerOperator_smul_smul_eq_mul_conj_smul {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (α β : ℂ) (a : Wp) (b : Wq) :
    rk1 (α • a) (β • b) = (α * (starRingEnd ℂ) β) • rk1 a b := by
  ext η
  rw [ContinuousLinearMap.smul_apply, rankOneInnerOperator_apply, rankOneInnerOperator_apply, inner_smul_left, smul_smul, smul_smul]
  congr 1
  ring

private theorem Afun_eq_inner_smul_of_isEll {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat k r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {μS : Measure (Mt k r)}
    {σ : Mat k r → (H →L[ℂ] H)} {w : H} {l : H → Wp} (hl : IsEll z ψ π μS σ (DD σ w) l)
    {w₀ : H} (hw₀ : w₀ ∈ DD σ w) (ξ : Wp) {x : Mat k r} (hx : x ∈ GG k r) :
    Afun ψ π μS σ w w₀ ξ x = ⟪l w₀, ξ⟫_ℂ • l (σ x w) := by
  unfold Afun
  rw [hl.2.2 _ (mem_DD σ w hx) _ hw₀, rankOneInnerOperator_apply]

theorem iint_eq_ell : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (l : H → Wp) (l' : H → Wq), IsEll z (psiGen k r z c) π μS σ (DD σ w) l → IsEll z' (psiGen k r z' c') π' μS' σ (DD σ w) l' → ∀ γ ∈ Greg k r z z', Integrable (fun x : Mt k r => rk1 (l (σ (Matrix.of x) w)) (l' (σ (γ⁻¹ * Matrix.of x) w))) μG ∧ ∀ w₀ ∈ DD σ w, ∀ w₀' ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ w₀' w₀ ξ ξ' γ = (⟪l w₀, ξ⟫_ℂ * ⟪ξ', l' w₀'⟫_ℂ * (d : ℂ)) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) γ := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' l l' hl hl' γ hγ
  have hHaar := hStd.2.2.2.2.1
  have hd : (0 : ℝ) < d := hStd.2.2.2.2.2.1.1
  have h0 : μG {x | Matrix.of x ∉ GG k r} = 0 := by
    first
    | exact hHaar.1
    | exact hHaar.2.2.1
  have hGG : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := ae_iff.2 h0
  have hU : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
  have hgrp := uHGroup _ (Hpk k r) hU
  have hγG : γ ∈ GG k r := Greg_subset z z' hγ
  have hγi : γ⁻¹ ∈ GG k r := (hgrp.2.2 γ hγG).2
  have hae : ∀ w₀ ∈ DD σ w, ∀ w₀' ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq),
      (fun x : Mt k r => rk1 (Afun (psiGen k r z c) π μS σ w w₀ ξ (Matrix.of x))
        (Afun (psiGen k r z' c') π' μS' σ w w₀' ξ' (γ⁻¹ * Matrix.of x))) =ᵐ[μG]
      fun x => (⟪l w₀, ξ⟫_ℂ * (starRingEnd ℂ) ⟪l' w₀', ξ'⟫_ℂ) •
        rk1 (l (σ (Matrix.of x) w)) (l' (σ (γ⁻¹ * Matrix.of x) w)) := by
    intro w₀ hw₀ w₀' hw₀' ξ ξ'
    filter_upwards [hGG] with x hx
    rw [Afun_eq_inner_smul_of_isEll hl hw₀ ξ hx, Afun_eq_inner_smul_of_isEll hl' hw₀' ξ' (hgrp.2.1 _ hγi _ hx), rankOneInnerOperator_smul_smul_eq_mul_conj_smul]
  obtain ⟨u, hu, hlu⟩ := hl.2.1
  obtain ⟨u', hu', hlu'⟩ := hl'.2.1
  have hint : Integrable
      (fun x : Mt k r => rk1 (l (σ (Matrix.of x) w)) (l' (σ (γ⁻¹ * Matrix.of x) w))) μG := by
    obtain ⟨-, hI, -⟩ := GlobalTheory.T.besselOrbitalIntegral_eq_inv_deg_smul k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' u hu u' hu'
      (l u) (l' u') γ hγ
    have hc : (⟪l u, l u⟫_ℂ * (starRingEnd ℂ) ⟪l' u', l' u'⟫_ℂ) ≠ 0 :=
      mul_ne_zero (inner_self_ne_zero.2 hlu) ((map_ne_zero _).2 (inner_self_ne_zero.2 hlu'))
    refine (hI.smul (⟪l u, l u⟫_ℂ * (starRingEnd ℂ) ⟪l' u', l' u'⟫_ℂ)⁻¹).congr ?_
    filter_upwards [hae u hu u' hu' (l u) (l' u')] with x hx
    rw [Pi.smul_apply, hx, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨hint, ?_⟩
  intro w₀ hw₀ w₀' hw₀' ξ ξ'
  obtain ⟨-, -, hO⟩ := GlobalTheory.T.besselOrbitalIntegral_eq_inv_deg_smul k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' w₀ hw₀ w₀' hw₀'
    ξ ξ' γ hγ
  have hO2 : OO μG (Afun (psiGen k r z c) π μS σ w w₀ ξ) (Afun (psiGen k r z' c') π' μS' σ w w₀' ξ') γ =
      (⟪l w₀, ξ⟫_ℂ * (starRingEnd ℂ) ⟪l' w₀', ξ'⟫_ℂ) • OO μG (fun x => l (σ x w)) (fun x => l' (σ x w)) γ := by
    unfold OO
    rw [integral_congr_ae (hae w₀ hw₀ w₀' hw₀' ξ ξ'), integral_smul]
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hO2, eq_inv_smul_iff₀ hdne] at hO
  rw [← hO, smul_smul, inner_conj_symm]
  congr 1
  ring

end GlobalTheory.SgInf.EllName
