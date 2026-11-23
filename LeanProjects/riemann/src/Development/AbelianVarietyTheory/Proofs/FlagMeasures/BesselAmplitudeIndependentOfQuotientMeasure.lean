import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralEqOfQuotientMeasuresBesselUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodularStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SnMass.AmpUniq

theorem isQuotMeas_smul {k r : ℕ} {μG μR ν : Measure (Mt k r)} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (h : IsQuotMeas μG (c • μR) ν) : IsQuotMeas μG μR (c • ν) := by
  intro f hf
  rw [h f hf]
  simp only [lintegral_smul_measure, smul_eq_mul]
  exact lintegral_const_mul' _ _ hc

theorem equiv_N {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat k r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} {Φ : Mat k r → Wp}
    (hπ : IsURepOn (UWset k r z) π) (hΦ : IsSPsiEquiv z ψ π Φ) {n : Mat k r} (hn : n ∈ Nset k r)
    {x : Mat k r} (hx : x ∈ GG k r) : Φ (n * x) = ψ n • Φ x := by
  have h1 : (1 : Mat k r) ∈ UWset k r z := (isClosedSub_UWset (k := k) (r := r) z).2.2.1
  have e := hΦ 1 h1 n hn x hx
  rw [hπ.1.1, one_mul, ContinuousLinearMap.one_apply] at e
  exact e

theorem amp_uniq : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (ψ ψ' : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (cN : ℝ), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsURepOn (UWset k r z) π → IsURepOn (UWset k r z') π' → (∀ n ∈ Nset k r, ‖ψ n‖ = 1 ∧ ‖ψ' n‖ = 1) → IsSPsiEquiv z ψ π Φ → IsSPsiEquiv z' ψ' π' Φ' → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → ∀ (γ : Mat k r) (μG μR ν ν' : Measure (Mt k r)) (t : ℝ), γ ∈ GG k r → (∀ ρ ∈ Rset k r γ, ψ (γ * ρ * γ⁻¹) = ψ' ρ) → IsHaarOn (GG k r) μG → IsHaarOn (Rset k r γ) μR → 0 < t → IsQuotMeas μG μR ν → IsQuotMeas μG (ENNReal.ofReal t • μR) ν' → ampJ ν cN Φ Φ' γ = (t : ℂ) • ampJ ν' cN Φ Φ' γ := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ z z' ψ ψ' π π' Φ Φ' cN _ _ _ _ hπ hπ' hψ hΦ hΦ' hc hc' γ μG μR ν ν' t hγ
    hψγ hG hR ht hν hν'
  obtain ⟨hRc, hRu⟩ := GlobalTheory.T.unipotentRadical_inter_conjugate_closed_unimodular k r γ hγ
  have hν₂ : IsQuotMeas μG μR (ENNReal.ofReal t • ν') := isQuotMeas_smul ENNReal.ofReal_ne_top hν'
  have hGm : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := (isClosedSub_GG (k := k) (r := r)).2.2.2.1
  let F : Mat k r → (Wq →L[ℂ] Wp) := fun g => (innerSL ℂ (Φ' g)).smulRight (Φ (γ * g))
  have hFc : ContinuousOn F (GG k r) := by
    have h1 : ContinuousOn (fun g => innerSL ℂ (Φ' g)) (GG k r) :=
      (innerSL ℂ).continuous.comp_continuousOn hc'
    have h2 : ContinuousOn (fun g => Φ (γ * g)) (GG k r) :=
      hc.comp (continuous_const.mul continuous_id).continuousOn fun g hg => hGm γ hγ g hg
    exact (ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous₂.comp_continuousOn (h1.prodMk h2)
  have hFi : ∀ ρ ∈ Rset k r γ, ∀ x ∈ GG k r, F (ρ * x) = F x := by
    intro ρ hρ x hx
    have hρN : ρ ∈ Nset k r := hρ.1
    have hρc : γ * ρ * γ⁻¹ ∈ Nset k r := hρ.2
    have e1 : Φ' (ρ * x) = ψ' ρ • Φ' x := equiv_N hπ' hΦ' hρN hx
    have e2 : γ * (ρ * x) = γ * ρ * γ⁻¹ * (γ * x) := by
      rw [show γ * ρ * γ⁻¹ * (γ * x) = γ * ρ * (γ⁻¹ * γ) * x by simp only [Matrix.mul_assoc],
        Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG hγ), Matrix.mul_one, Matrix.mul_assoc]
    have e3 : Φ (γ * (ρ * x)) = ψ' ρ • Φ (γ * x) := by
      rw [e2, equiv_N hπ hΦ hρc (hGm γ hγ x hx), hψγ ρ hρ]
    have hn : ‖ψ' ρ‖ = 1 := (hψ ρ hρN).2
    ext w
    simp only [F, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, e1, e3, inner_smul_left,
      smul_smul]
    congr 1
    calc (starRingEnd ℂ) (ψ' ρ) * inner ℂ (Φ' x) w * ψ' ρ
        = ((starRingEnd ℂ) (ψ' ρ) * ψ' ρ) * inner ℂ (Φ' x) w := by ring
      _ = inner ℂ (Φ' x) w := by rw [Complex.conj_mul', hn]; simp
  have key := (GlobalTheory.T.integral_eq_of_quotientMeasures_besselUnitary k r (Rset k r γ) μG μR ν (ENNReal.ofReal t • ν') hRc hG hR (hRu μR hR) hν hν₂
    (Wq →L[ℂ] Wp) F hFc hFi).2
  rw [integral_smul_measure, ENNReal.toReal_ofReal ht.le] at key
  change (cN : ℂ)⁻¹ • ∫ x, F (Matrix.of x) ∂ν = (t : ℂ) • ((cN : ℂ)⁻¹ • ∫ x, F (Matrix.of x) ∂ν')
  rw [key, Complex.coe_smul, smul_comm]

end GlobalTheory.SnMass.AmpUniq
