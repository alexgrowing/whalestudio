import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdSm
import Formalism.SharpRestriction.CuspSpanNormBounds.DoubleBoundAndExtensionOfSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvSig
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPsi

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW Formalism.MainNotions.InverseNormDecayBounds Formalism.MainNotions.BridgeLemma₄

variable {k r : ℕ}

theorem gN_cont : Continuous (Formalism.FourierDecayAlt.B.gN : Mx k r → ℝ) := by
  unfold Formalism.FourierDecayAlt.B.gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

theorem intG_of_lint {μ : Measure (Mt k r)} {A : ℝ}
    (h : ∫⁻ x : Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)) ∂μ < ∞) :
    Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)) μ := by
  have h1 : Continuous (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x)) := gN_cont.comp PI.WUN.continuous_of
  have h0 : ∀ x : Mt k r, 0 ≤ Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A) := fun x =>
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  refine ⟨(h1.measurable.pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)]
  exact h

theorem intS_of_lint {μ : Measure (Mt k r × Mt k r)} {A : ℝ}
    (h : ∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) ∂μ < ∞) :
    Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A)) μ := by
  have hm : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mx k r) * Matrix.of p.2) :=
    (continuous_fst : Continuous (fun p : Mt k r × Mt k r => p.1)).matrix_mul continuous_snd
  have h1 : Continuous (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2)) :=
    gN_cont.comp hm
  have h0 : ∀ p : Mt k r × Mt k r, 0 ≤ Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-A) := fun p =>
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  refine ⟨(h1.measurable.pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)]
  exact h

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem normIdSm_DD (hHW : Cv.HaarWAll) (hHN : Cv.HaarNAll)
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hlam : IsHCParam lam) (hds : IsDSHpk k r ε lam σ) {μG : Measure (Mt k r)} (hHaar : IsHaarOn (UH (Hpk k r)) μG)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {u0 : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsHCTypeW k r z u0 π) {μW : Measure (Mt k r)}
    (hμW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1) {κ : ℝ≥0∞} (hκ : 0 < κ) (hκt : κ ≠ ⊤)
    {νq : Measure (Mt k r)} (hq : IsQuotMeas μG (Formalism.MainNotions.OnePlaceEstimates.muSof μW (haarLie (Nset k r) κ)) νq) (c : ℂ)
    (hS : SchurOn μG σ) {w0 : H} (hw0 : IsLowUnitH k r ε lam σ w0) {a : ℝ} (ha : 1 ≤ a)
    (hD : DiagonalMatrixCoefficientPowerDecay σ w0 a) (hI : DecInfAt σ a)
    (hGg : ∫⁻ x : Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-((a - 1) / 2))) ∂μG < ∞)
    (hSS : ∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-((a - 1) / 2)))
      ∂(μW.prod (haarLie (Nset k r) κ)) < ∞)
    {u v : H} (hu : u ∈ smoothVecs (k := k) (r := r) σ) (hu0 : u ≠ 0) (hv : v ∈ DDsp σ w0) (ξ : Wp) :
    haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
    Integrable (fun x : Mt k r =>
      ‖(∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ (σ (Matrix.of x) u) v p ∂(μW.prod (haarLie (Nset k r) κ))) ξ‖ ^ 2) νq ∧
    l2SG νq (fun g => (∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ (σ g u) v p ∂(μW.prod (haarLie (Nset k r) κ))) ξ) =
      ENNReal.ofReal (‖u‖ ^ 2 *
        (⟪(∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ v v p ∂(μW.prod (haarLie (Nset k r) κ))) ξ, ξ⟫_ℂ).re /
          fdegH μG σ u) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : SigmaFinite μW := hμW.1
  have hG : GHyp z π μW (haarLie (Nset k r) κ) μG νq σ :=
    ⟨⟨ε, lam, hlam, hds⟩, hHaar, ⟨hz, hT⟩, ⟨u0, hπ⟩, ⟨hμW, hW1⟩, ⟨κ, hκ, hκt, rfl⟩, hq⟩
  have hWf := hHW _ _ z μW hz hT hμW hW1
  have hNf := hHN _ _ z κ hz hT
  have hM : Cv.MeasF z π μW (haarLie (Nset k r) κ) :=
    Cv.measF_of hWf.1 hWf.2 hμW.2.2.1 hNf.1 hNf.2.1 hNf.2.2 (Cv.piContAll _ _ z u0 Wp π hz hT hπ)
  obtain ⟨hint, -, hl⟩ := normId_smDD (c := c) hG (Cv.grpAll _ _ z) (Cv.sigAll _ _ _ _ H σ hds)
    (Cv.piAll _ _ z u0 Wp π hz hT hπ) (Cv.psiAll _ _ z c hz) hM hS hds hw0 ha hD hI
    (intG_of_lint hGg) (intS_of_lint hSS) hu hu0 hv ξ
  refine ⟨hint, ?_⟩
  unfold l2SG
  exact hl

theorem normIdSm_K (hHW : Cv.HaarWAll) (hHN : Cv.HaarNAll)
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hlam : IsHCParam lam) (hds : IsDSHpk k r ε lam σ) {μG : Measure (Mt k r)} (hHaar : IsHaarOn (UH (Hpk k r)) μG)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {u0 : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsHCTypeW k r z u0 π) {μW : Measure (Mt k r)}
    (hμW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1) {κ : ℝ≥0∞} (hκ : 0 < κ) (hκt : κ ≠ ⊤)
    {νq : Measure (Mt k r)} (hq : IsQuotMeas μG (Formalism.MainNotions.OnePlaceEstimates.muSof μW (haarLie (Nset k r) κ)) νq) (c : ℂ)
    (hS : SchurOn μG σ) {a : ℝ} (ha : 1 ≤ a) (hI : DecInfAt σ a)
    (hGg : ∫⁻ x : Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-((a - 1) / 2))) ∂μG < ∞)
    (hSS : ∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-((a - 1) / 2)))
      ∂(μW.prod (haarLie (Nset k r) κ)) < ∞)
    {u v : H} (hu : u ∈ smoothVecs (k := k) (r := r) σ) (hu0 : u ≠ 0)
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (hvK : IsKFinHpk (k := k) (r := r) σ v) (ξ : Wp) :
    haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
    Integrable (fun x : Mt k r =>
      ‖(∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ (σ (Matrix.of x) u) v p ∂(μW.prod (haarLie (Nset k r) κ))) ξ‖ ^ 2) νq ∧
    l2SG νq (fun g => (∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ (σ g u) v p ∂(μW.prod (haarLie (Nset k r) κ))) ξ) =
      ENNReal.ofReal (‖u‖ ^ 2 *
        (⟪(∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ v v p ∂(μW.prod (haarLie (Nset k r) κ))) ξ, ξ⟫_ℂ).re /
          fdegH μG σ u) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : SigmaFinite μW := hμW.1
  have hG : GHyp z π μW (haarLie (Nset k r) κ) μG νq σ :=
    ⟨⟨ε, lam, hlam, hds⟩, hHaar, ⟨hz, hT⟩, ⟨u0, hπ⟩, ⟨hμW, hW1⟩, ⟨κ, hκ, hκt, rfl⟩, hq⟩
  have hWf := hHW _ _ z μW hz hT hμW hW1
  have hNf := hHN _ _ z κ hz hT
  have hM : Cv.MeasF z π μW (haarLie (Nset k r) κ) :=
    Cv.measF_of hWf.1 hWf.2 hμW.2.2.1 hNf.1 hNf.2.1 hNf.2.2 (Cv.piContAll _ _ z u0 Wp π hz hT hπ)
  obtain ⟨hint, -, hl⟩ := normId_smK (c := c) hG (Cv.grpAll _ _ z) (Cv.sigAll _ _ _ _ H σ hds)
    (Cv.piAll _ _ z u0 Wp π hz hT hπ) (Cv.psiAll _ _ z c hz) hM hS ha hI
    (intG_of_lint hGg) (intS_of_lint hSS) hu hu0 hv hvK ξ
  refine ⟨hint, ?_⟩
  unfold l2SG
  exact hl

theorem normId_DD_set (hHW : Cv.HaarWAll) (hHN : Cv.HaarNAll)
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hlam : IsHCParam lam) (hds : IsDSHpk k r ε lam σ) {μG : Measure (Mt k r)} (hHaar : IsHaarOn (UH (Hpk k r)) μG)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {u0 : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsHCTypeW k r z u0 π) {μW : Measure (Mt k r)}
    (hμW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1) {κ : ℝ≥0∞} (hκ : 0 < κ) (hκt : κ ≠ ⊤)
    {νq : Measure (Mt k r)} (hq : IsQuotMeas μG (Formalism.MainNotions.OnePlaceEstimates.muSof μW (haarLie (Nset k r) κ)) νq) (c : ℂ)
    (hS : SchurOn μG σ) {w0 : H} {a : ℝ} (ha : 0 ≤ a) (hD : DiagonalMatrixCoefficientPowerDecay σ w0 a)
    (hGg : ∫⁻ x : Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-(a / 2))) ∂μG < ∞)
    (hSS : ∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(a / 2)))
      ∂(μW.prod (haarLie (Nset k r) κ)) < ∞)
    {u v : H} (hu : u ∈ DDsp σ w0) (hu0 : u ≠ 0) (hv : v ∈ DDsp σ w0) (ξ : Wp) :
    haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
    Integrable (fun x : Mt k r =>
      ‖(∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ (σ (Matrix.of x) u) v p ∂(μW.prod (haarLie (Nset k r) κ))) ξ‖ ^ 2) νq ∧
    l2SG νq (fun g => (∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ (σ g u) v p ∂(μW.prod (haarLie (Nset k r) κ))) ξ) =
      ENNReal.ofReal (‖u‖ ^ 2 *
        (⟪(∫ p, Formalism.MainNotions.DoubleDerivativeSmoothness.FI z c π σ v v p ∂(μW.prod (haarLie (Nset k r) κ))) ξ, ξ⟫_ℂ).re /
          fdegH μG σ u) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : SigmaFinite μW := hμW.1
  have hG : GHyp z π μW (haarLie (Nset k r) κ) μG νq σ :=
    ⟨⟨ε, lam, hlam, hds⟩, hHaar, ⟨hz, hT⟩, ⟨u0, hπ⟩, ⟨hμW, hW1⟩, ⟨κ, hκ, hκt, rfl⟩, hq⟩
  have hWf := hHW _ _ z μW hz hT hμW hW1
  have hNf := hHN _ _ z κ hz hT
  have hM : Cv.MeasF z π μW (haarLie (Nset k r) κ) :=
    Cv.measF_of hWf.1 hWf.2 hμW.2.2.1 hNf.1 hNf.2.1 hNf.2.2 (Cv.piContAll _ _ z u0 Wp π hz hT hπ)
  obtain ⟨hint, -, hl⟩ := normId_DD (c := c) hG (Cv.grpAll _ _ z) (Cv.sigAll _ _ _ _ H σ hds)
    (Cv.piAll _ _ z u0 Wp π hz hT hπ) (Cv.psiAll _ _ z c hz) hM hS ha hD
    (intG_of_lint hGg) (intS_of_lint hSS) hu hu0 hv ξ
  refine ⟨hint, ?_⟩
  unfold l2SG
  exact hl

end PI.WBL.NIS
