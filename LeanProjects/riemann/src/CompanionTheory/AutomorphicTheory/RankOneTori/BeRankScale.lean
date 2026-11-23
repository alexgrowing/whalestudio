import CompanionTheory.AutomorphicTheory.RankOneEstimates.RankOne
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.SigmaFiniteOfUnfold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.FourierDecayAlt.P
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainStatements.RankOne

variable {k r : ℕ}

theorem be_scale {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hz : inWb k r z)
    (h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z) (h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (c : ℂ) (u v : H) :
    Formalism.FourierDecayAlt.ThreeDimData.be ((τ : ℂ) • z) ((κ : ℂ) * c) (fun x => π (cjI k r κ τ x)) σ (μW.map (cjT k r κ τ))
              (μN.map (cjT k r κ τ)) u v =
      Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW μN (σ (dM k r κ τ) u) (σ (dM k r κ τ) v) := by
  unfold Formalism.FourierDecayAlt.ThreeDimData.be
  rw [Measure.map_prod_map _ _ measurable_cjT measurable_cjT]
  have e : Prod.map (cjT k r κ τ) (cjT k r κ τ) = ⇑((cjE (k := k) (r := r) hκ hτ).prodCongr (cjE hκ hτ)) := rfl
  rw [e, integral_map_equiv]
  refine integral_congr_ae ?_
  have a1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.quasiMeasurePreserving_fst.ae h1
  have a2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.quasiMeasurePreserving_snd.ae h2
  filter_upwards [a1, a2] with p hp1 hp2
  show Formalism.FourierDecayAlt.ThreeDimData.beInt _ _ _ σ u v (cjT k r κ τ p.1, cjT k r κ τ p.2) = _
  have hd := dM_mem_UH (k := k) (r := r) hκ hτ
  have hdi := dMi_mem_UH (k := k) (r := r) hκ hτ
  have hx : Matrix.of p.1 * Matrix.of p.2 ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul hp1.1 hp2.1
  simp only [Formalism.FourierDecayAlt.ThreeDimData.beInt, of_cjT]
  rw [psi_cj hκ hτ hz, ← cj_inv hκ hτ, cjI_cj hκ hτ, ← cj_mul hκ hτ]
  congr 2
  unfold cj
  rw [TranslationBesselVanishing.sigma_mul hσ (WeylGroupFacts.uh_mul hdi hx) hd, TranslationBesselVanishing.sigma_mul hσ hdi hx]
  simp only [ContinuousLinearMap.comp_apply]
  rw [MatrixMultiplicationContinuity.sigma_inner hσ hdi, dMi_inv hκ hτ]

theorem be_rank_scale (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {μW : Measure (Mt k r)}
    (hl : IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) (hW : IsHaarOn (UWset k r z) μW) {κN : ℝ≥0∞} (h0 : κN ≠ 0) (h1 : κN ≠ ⊤)
    {κ₀ : ℝ} (hκ₀ : 0 < κ₀) :
    ∃ l : H → Wp, ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      Formalism.FourierDecayAlt.ThreeDimData.be z (cOfDpsi (κ₀ : ℂ)) π σ μW (haarLie (Nset k r) κN) w v = (innerSL ℂ (l v)).smulRight (l w) := by
  have hκ : 0 < κ₀⁻¹ := inv_pos.2 hκ₀
  have hτ : (0 : ℝ) < 1 := one_pos
  have : SigmaFinite μW := hW.1
  have : SFinite (haarLie (Nset k r) κN) := sFinite_haarLie _ _
  have hc : ((κ₀⁻¹ : ℝ) : ℂ) * cOfDpsi (κ₀ : ℂ) = cStd := by
    have : (κ₀ : ℂ) ≠ 0 := by exact_mod_cast hκ₀.ne'
    unfold cOfDpsi cStd
    push_cast
    field_simp
  have hN : IsHaarOn (Nset k r) ((haarLie (Nset k r) κN).map (cjT k r κ₀⁻¹ 1)) := by
    rw [map_haarLie_N hκ hτ]
    exact Formalism.MainNotions.BridgeCSB.haarLieN k r _ (mul_ne_zero h0 (ENNReal.ofReal_pos.2 (deltaN_pos hκ hτ)).ne')
      (ENNReal.mul_ne_top h1 ENNReal.ofReal_ne_top)
  obtain ⟨L, hL⟩ := CompanionTheory.FamilyDerivativeExpansion.M1.be_rank_one (z := ((1 : ℝ) : ℂ) • z) (π := fun x => π (cjI k r κ₀⁻¹ 1 x)) hk hl hσ hg hh
    (inWb_smul hz _) (by rw [Tz_smul]; simpa using hT) (isHCTypeW_cjI hκ hτ hz hπ) (isHaarOn_map_cjT hκ hτ hz hW) hN
  have hd := dM_mem_UH (k := k) (r := r) hκ hτ
  have hdi := dMi_mem_UH (k := k) (r := r) hκ hτ
  have hcan : ∀ x : H, σ (dM k r κ₀⁻¹ 1) (σ (dMi k r κ₀⁻¹ 1) x) = x := fun x => by
    rw [← ContinuousLinearMap.comp_apply, ← TranslationBesselVanishing.sigma_mul hσ hd hdi, dM_mul_dMi hκ hτ, (MatrixMultiplicationContinuity.sigma_facts hσ).1]
    rfl
  refine ⟨fun x => L (σ (dMi k r κ₀⁻¹ 1) x), fun w hw v hv => ?_⟩
  have e := be_scale (π := π) hσ hz (Formalism.MainNotions.S.Pv.AmpDDPf.ae_mem_sk hW) (Formalism.MainNotions.S.Pv.AmpDDPf.ae_mem_haarLieN κN) hκ hτ
    (cOfDpsi (κ₀ : ℂ)) (σ (dMi k r κ₀⁻¹ 1) w) (σ (dMi k r κ₀⁻¹ 1) v)
  rw [hcan, hcan, hc] at e
  rw [← e]
  exact (hL _ (TranslationBesselVanishing.smooth_translate hσ hw hdi) _ (TranslationBesselVanishing.smooth_translate hσ hv hdi)).2

end Formalism.MainStatements.RankOne
