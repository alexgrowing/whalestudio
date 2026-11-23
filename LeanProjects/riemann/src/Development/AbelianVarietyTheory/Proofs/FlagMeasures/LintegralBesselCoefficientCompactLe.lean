import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormIdentityBesselCoefficientQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralCompactLeQuotientMeasureBesselStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWN
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsQuotMeasSset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem lint_Afun_compact_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u ∈ DD σ w, AEStronglyMeasurable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide v hv ξ K hK
  classical
  have hStd' := hStd
  have hSide' := hSide
  obtain ⟨-, hrep, -, -, hHaar, hSchur, -, hDecay, -⟩ := hStd'
  obtain ⟨hz, hT, hπ, hμS, -⟩ := hSide'
  obtain ⟨hclG, -, -, hclS, -⟩ := GlobalTheory.SgInf.closedSub_groups k r z hz hT
  have hUni : IsUnimod (Sset k r z) μS := ((GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT μS).1) hμS
  obtain ⟨ν, hν⟩ := exists_isQuotMeas_Sset k r z μG μS hz hT hHaar hμS
  obtain ⟨C₀, hC₀, hC⟩ := GlobalTheory.T.lintegral_compact_le_quotientMeasure_bessel k r (Sset k r z) μG μS ν K hclS hHaar hμS hUni hν hK
  have hstab : ∀ g ∈ GG k r, ∀ x ∈ DD σ w, σ g x ∈ DD σ w :=
    (GlobalTheory.SgInfDD.DD_stable_dense k r σ w hrep).1
  have hD1 := fun u (hu : u ∈ DD σ w) => GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide
    (DD σ w : Set H) (fun g hg x hx => hstab g hg x hx) hDecay u hu v hv
  have hPi := (GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hz hT hπ).2.1
  have hD3 := fun u (hu : u ∈ DD σ w) =>
    GlobalTheory.T.norm_identity_besselCoefficient_quotient k r σ w a μG d z c π μS hStd hSide ν hν u hu u hu v hv ξ
  set ψ := psiGen k r z c with hψ
  set bc : ℂ := ⟪ξ, be ψ π μS σ v v ξ⟫_ℂ with hbc
  refine ⟨C₀.toReal * bc.re / d, fun u hu => ?_⟩
  set A : Mt k r → Wp := fun x => Afun ψ π μS σ u v ξ (Matrix.of x) with hA
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  set GM : Set (Mt k r) := {x | Matrix.of x ∈ GG k r} with hGM
  have hGMc : IsClosed GM := hclG.2.1.preimage hof
  have hAc : ContinuousOn A GM := by
    have h1 : ContinuousOn (fun x : Mat k r => Afun ψ π μS σ u v ξ x) (GG k r) :=
      (hD1 u hu).2.2.2.clm_apply continuousOn_const
    exact h1.comp hof.continuousOn (fun x hx => hx)
  have hae : ∀ᵐ x ∂μG, x ∈ GM := by
    rw [ae_iff]; exact hHaar.2.2.1
  refine ⟨?_, ?_⟩
  · have h1 : AEStronglyMeasurable A (μG.restrict GM) :=
      hAc.aestronglyMeasurable hGMc.measurableSet
    rw [Measure.restrict_eq_self_of_ae_mem hae] at h1
    exact h1.restrict
  set F : Mt k r → ENNReal := GM.indicator (fun x => (‖A x‖₊ : ENNReal) ^ 2) with hF
  have hFm : Measurable F := by
    have h1 : ContinuousOn (fun x => (‖A x‖₊ : ENNReal) ^ 2) GM := by
      have h0 : ContinuousOn (fun x => (‖A x‖₊ : ENNReal)) GM :=
        (ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn hAc
      exact (ENNReal.continuous_pow 2).comp_continuousOn h0
    have h2 := ContinuousOn.measurable_piecewise h1
      (continuousOn_const (c := (0 : ENNReal)) (s := GMᶜ)) hGMc.measurableSet
    have h3 : F = GM.piecewise (fun x => (‖A x‖₊ : ENNReal) ^ 2) (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ GM <;> simp [hF, hx]
    rw [h3]; exact h2
  have hFinv : ∀ s ∈ Sset k r z, ∀ x, F (lmulM s x) = F x := by
    intro s hs x
    have hsG : s ∈ GG k r := hclS.1 hs
    have hmem : lmulM s x ∈ GM ↔ x ∈ GM := by
      constructor
      · intro h
        have h1 : s⁻¹ * (s * (Matrix.of x : Mat k r)) ∈ GG k r :=
          hclG.2.2.2.1 _ (hclG.2.2.2.2 _ hsG) _ h
        have h2 : s⁻¹ * (s * (Matrix.of x : Mat k r)) = Matrix.of x := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG hsG), Matrix.one_mul]
        rw [h2] at h1; exact h1
      · intro h; exact hclG.2.2.2.1 _ hsG _ h
    by_cases hx : x ∈ GM
    · have hx' := hmem.2 hx
      rw [hF, Set.indicator_of_mem hx', Set.indicator_of_mem hx]
      have hAeq : A (lmulM s x) = PiS ψ π s (A x) := by
        show be ψ π μS σ (σ (s * Matrix.of x) u) v ξ =
          PiS ψ π s (be ψ π μS σ (σ (Matrix.of x) u) v ξ)
        have hm : σ (s * Matrix.of x) = (σ s).comp (σ (Matrix.of x)) := hrep.1.2 s hsG _ hx
        have hxu : σ (Matrix.of x) u ∈ DD σ w := hstab _ hx u hu
        have he := ((hD1 _ hxu).2.1 s hs).1
        rw [hm]
        show be ψ π μS σ (σ s (σ (Matrix.of x) u)) v ξ = _
        rw [he]; rfl
      have hn : ‖PiS ψ π s (A x)‖₊ = ‖A x‖₊ := Subtype.ext (hPi.2.1 s hs _)
      rw [hAeq, hn]
    · have hx' : lmulM s x ∉ GM := fun h => hx (hmem.1 h)
      rw [hF, Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]
  obtain ⟨-, -, hL2, hnorm, hb0, hbim⟩ := hD3 u hu
  have hint : Integrable (fun x => ‖A x‖ ^ 2) ν := hL2.integrable_norm_pow (by norm_num)
  have hval : ∫ x, ‖A x‖ ^ 2 ∂ν = ‖u‖ ^ 2 * bc.re / d := by
    have h1 : ∫ x, ⟪A x, A x⟫_ℂ ∂ν = ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h2 : bc = (bc.re : ℂ) := by
      apply Complex.ext <;> simp [hbim]
    have h3 : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h4 : ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖u‖ ^ 2 * bc.re / d : ℝ) : ℂ) := by
      rw [← h1]
      refine hnorm.trans ?_
      rw [h3]
      push_cast
      rw [← h2]
    exact_mod_cast h4
  have hlin : ∫⁻ x, (‖A x‖₊ : ENNReal) ^ 2 ∂ν = ENNReal.ofReal (‖u‖ ^ 2 * bc.re / d) := by
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ← enorm_eq_nnnorm, ofReal_norm_eq_enorm]
  calc ∫⁻ x in K, (‖A x‖₊ : ENNReal) ^ 2 ∂μG = ∫⁻ x in K, F x ∂μG := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hae] with x hx
        rw [hF, Set.indicator_of_mem hx]
    _ ≤ C₀ * ∫⁻ x, F x ∂ν := hC F hFm hFinv
    _ ≤ C₀ * ∫⁻ x, (‖A x‖₊ : ENNReal) ^ 2 ∂ν := by
        refine mul_le_mul_right ?_ _
        exact lintegral_mono fun x => Set.indicator_le_self _ _ x
    _ = ENNReal.ofReal (C₀.toReal * bc.re / d * ‖u‖ ^ 2) := by
        rw [hlin]
        have hC₁ : C₀ = ENNReal.ofReal C₀.toReal := (ENNReal.ofReal_toReal hC₀.ne).symm
        conv_lhs => rw [hC₁]
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        congr 1; ring

end GlobalTheory.SgInf
