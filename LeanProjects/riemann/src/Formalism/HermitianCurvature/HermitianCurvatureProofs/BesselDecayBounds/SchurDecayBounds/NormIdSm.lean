import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdDec
import Formalism.SharpRestriction.CuspSpanNormBounds.KfinOfMemLowKSub

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW Formalism.MainNotions.InverseNormDecayBounds Formalism.MainNotions.BridgeLemma₄

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

theorem gN_lshift {x y : Mx k r} (hx : x ∈ UH (Hpk k r)) (hy : y ∈ UH (Hpk k r)) {a : ℝ} (ha : 0 ≤ a) :
    Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (-a) ≤ Formalism.FourierDecayAlt.B.gN y ^ a * Formalism.FourierDecayAlt.B.gN x ^ (-a) := by
  have hUnit : IsUnit y.det := by
    have h1 : yᴴ * Hpk k r * y = Hpk k r := hy
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    have hH := Formalism.MainNotions.BesselShellMomentBounds.Hpk_det_unit k r
    have h3 : (yᴴ).det * y.det = 1 := by
      apply hH.mul_left_cancel
      calc (Hpk k r).det * ((yᴴ).det * y.det) = (yᴴ).det * (Hpk k r).det * y.det := by ring
        _ = (Hpk k r).det := h2
        _ = (Hpk k r).det * 1 := (mul_one _).symm
    exact IsUnit.of_mul_eq_one ((yᴴ).det) (by rw [mul_comm]; exact h3)
  have hNI := Formalism.MainNotions.InverseNormDecayBounds.normInvP k r
  have hgx : 1 ≤ Formalism.FourierDecayAlt.B.gN x := (hNI.1 x hx).2
  have hgy : 1 ≤ Formalism.FourierDecayAlt.B.gN y := (hNI.1 y hy).2
  have hsub : Formalism.FourierDecayAlt.B.gN x ≤ Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) := by
    have := hNI.2 y (y⁻¹ * x)
    rwa [Matrix.mul_nonsing_inv_cancel_left _ _ hUnit] at this
  have hlow : Formalism.FourierDecayAlt.B.gN x / Formalism.FourierDecayAlt.B.gN y ≤ Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) := by
    rw [div_le_iff₀ (by linarith)]
    linarith [mul_comm (Formalism.FourierDecayAlt.B.gN y) (Formalism.FourierDecayAlt.B.gN (y⁻¹ * x))]
  have h0x : 0 < Formalism.FourierDecayAlt.B.gN x := by linarith
  have h0y : 0 < Formalism.FourierDecayAlt.B.gN y := by linarith
  calc Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (-a) ≤ (Formalism.FourierDecayAlt.B.gN x / Formalism.FourierDecayAlt.B.gN y) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (div_pos h0x h0y) hlow (by linarith)
    _ = Formalism.FourierDecayAlt.B.gN y ^ a * Formalism.FourierDecayAlt.B.gN x ^ (-a) := by
        rw [Real.div_rpow h0x.le h0y.le, Real.rpow_neg h0y.le a, div_inv_eq_mul, mul_comm]

theorem decBd_mono {σ : Mx k r → (H →L[ℂ] H)} {a b : ℝ} {u' u : H} (hab : b ≤ a) (h : DecBd σ a u' u) :
    DecBd σ b u' u := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun x hx => ?_⟩
  have hg : 1 ≤ Formalism.FourierDecayAlt.B.gN x := ((Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).1 x hx).2
  calc ‖⟪u', σ x u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN x ^ (-a) := hC x hx
    _ ≤ max C 0 * Formalism.FourierDecayAlt.B.gN x ^ (-a) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hg (by linarith)) (le_max_right _ _)

theorem decBd_left {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) (hSg : Cv.SigU σ) {w0 u : H} {b : ℝ} (hb : 0 ≤ b) (h : DecBd σ b w0 u)
    {y : Mx k r} (hy : y ∈ UH (Hpk k r)) : DecBd σ b (σ y w0) u := by
  obtain ⟨C, hC⟩ := h
  have hNI := Formalism.MainNotions.InverseNormDecayBounds.normInvP k r
  have hUnit : ∀ g ∈ UH (Hpk k r), IsUnit g.det := by
    intro g hg
    have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    have hH := Formalism.MainNotions.BesselShellMomentBounds.Hpk_det_unit k r
    have h3 : (gᴴ).det * g.det = 1 := by
      apply hH.mul_left_cancel
      calc (Hpk k r).det * ((gᴴ).det * g.det) = (gᴴ).det * (Hpk k r).det * g.det := by ring
        _ = (Hpk k r).det := h2
        _ = (Hpk k r).det * 1 := (mul_one _).symm
    exact IsUnit.of_mul_eq_one ((gᴴ).det) (by rw [mul_comm]; exact h3)
  have hmul : ∀ a ∈ UH (Hpk k r), ∀ c ∈ UH (Hpk k r), a * c ∈ UH (Hpk k r) := by
    intro a ha c hc
    have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
    have hc' : cᴴ * Hpk k r * c = Hpk k r := hc
    show (a * c)ᴴ * Hpk k r * (a * c) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc cᴴ * aᴴ * Hpk k r * (a * c) = cᴴ * (aᴴ * Hpk k r * a) * c := by simp only [mul_assoc]
      _ = Hpk k r := by rw [ha', hc']
  have hinv : y⁻¹ ∈ UH (Hpk k r) := by
    have hd := hUnit y hy
    have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
    show (y⁻¹)ᴴ * Hpk k r * y⁻¹ = Hpk k r
    calc (y⁻¹)ᴴ * Hpk k r * y⁻¹ = (y⁻¹)ᴴ * (yᴴ * Hpk k r * y) * y⁻¹ := by rw [hy']
      _ = (y * y⁻¹)ᴴ * Hpk k r * (y * y⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [mul_assoc]
      _ = Hpk k r := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  refine ⟨max C 0 * Formalism.FourierDecayAlt.B.gN y ^ b, fun x hx => ?_⟩
  have hyx : y⁻¹ * x ∈ UH (Hpk k r) := hmul _ hinv _ hx
  have hsx : σ x = (σ y).comp (σ (y⁻¹ * x)) := by
    rw [← hSg.2.1 y hy _ hyx, Matrix.mul_nonsing_inv_cancel_left _ _ (hUnit y hy)]
  let li : H →ₗᵢ[ℂ] H := { toLinearMap := (σ y : H →ₗ[ℂ] H), norm_map' := hSg.2.2 y hy }
  have hin : ⟪σ y w0, σ x u⟫_ℂ = ⟪w0, σ (y⁻¹ * x) u⟫_ℂ := by
    rw [hsx, ContinuousLinearMap.comp_apply]
    exact li.inner_map_map w0 (σ (y⁻¹ * x) u)
  have hg1 : 1 ≤ Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) := (hNI.1 _ hyx).2
  rw [hin]
  calc ‖⟪w0, σ (y⁻¹ * x) u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (-b) := hC _ hyx
    _ ≤ max C 0 * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x) ^ (-b) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * (Formalism.FourierDecayAlt.B.gN y ^ b * Formalism.FourierDecayAlt.B.gN x ^ (-b)) :=
        mul_le_mul_of_nonneg_left (gN_lshift hx hy hb) (le_max_right _ _)
    _ = max C 0 * Formalism.FourierDecayAlt.B.gN y ^ b * Formalism.FourierDecayAlt.B.gN x ^ (-b) := by ring

theorem decBd_DD_left {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) (hSg : Cv.SigU σ) {w0 u : H} {b : ℝ} (hb : 0 ≤ b) (h : DecBd σ b w0 u) :
    ∀ v ∈ DDsp σ w0, DecBd σ b v u := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact decBd_left hds hSg hb h hg
  | zero => exact Formalism.MainNotions.InverseNormDecayBounds.decBd_zero_left σ b u
  | add x y _ _ hx hy => exact Formalism.MainNotions.InverseNormDecayBounds.decBd_add_left hx hy
  | smul c x _ hx => exact Formalism.MainNotions.InverseNormDecayBounds.decBd_smul_left c hx

theorem normId_of_bd {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG ν : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)}
    (hG : GHyp z π μW μN μG ν σ)
    (hGr : Cv.GrpF k r z) (hSg : Cv.SigU σ) (hPi : Cv.PiU z π) (hPs : Cv.PsiF k r z c) (hM : Cv.MeasF z π μW μN)
    (hS : SchurOn μG σ) {u v : H} (hu : u ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (huv : DecBd σ b v u) (hvv : DecBd σ b v v)
    (hGg : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-(b / 2))) μG)
    (hSS : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(b / 2)))
      (μW.prod μN))
    (ξ : Wp) :
    Integrable (fun x : Mt k r => ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2) ν ∧
    ∫ x, ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2 ∂ν =
      ‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u ∧
    ∫⁻ x, (‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖₊ : ℝ≥0∞) ^ 2 ∂ν =
      ENNReal.ofReal (‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u) := by
  obtain ⟨⟨ε, lam, -, hds⟩, hHaar, -, -, ⟨-, hW1⟩, ⟨κ0, -, -, hN⟩, -⟩ := id hG
  subst hN
  have : IsFiniteMeasure μW := ⟨by rw [hW1]; exact ENNReal.one_lt_top⟩
  have : SFinite μG := sfinite_haar hHaar
  obtain ⟨C, hC⟩ := huv
  obtain ⟨C', hC'⟩ := hvv
  have hI : ∀ x ∈ UH (Hpk k r), Integrable (beF z c π σ (σ x u) v) (μW.prod (haarLie (Nset k r) κ0)) :=
    fun x hx => int_beF_of_bd hds hGr hPi hM hb (bd_shift hSg hb hC hx) hSS
  have hIv : Integrable (beF z c π σ v v) (μW.prod (haarLie (Nset k r) κ0)) :=
    int_beF_of_bd hds hGr hPi hM hb hC' hSS
  have hD := dInt_of_bd hds hGr hHaar hM.1 hb hC hGg hSS
  obtain ⟨hint, heq⟩ := normId_pair hG hGr hSg hPi hPs hM hS hu hI hIv hD ξ
  refine ⟨hint, heq, ?_⟩
  rw [← heq, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)]
  apply lintegral_congr
  intro x
  simp only [ENNReal.ofReal_pow, norm_nonneg, ofReal_norm, enorm_eq_nnnorm]

theorem normId_DD {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG ν : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)}
    (hG : GHyp z π μW μN μG ν σ)
    (hGr : Cv.GrpF k r z) (hSg : Cv.SigU σ) (hPi : Cv.PiU z π) (hPs : Cv.PsiF k r z c) (hM : Cv.MeasF z π μW μN)
    (hS : SchurOn μG σ) {w0 : H} {a : ℝ} (ha : 0 ≤ a) (hD : DiagonalMatrixCoefficientPowerDecay σ w0 a)
    (hGg : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-(a / 2))) μG)
    (hSS : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(a / 2)))
      (μW.prod μN))
    {u v : H} (hu : u ∈ DDsp σ w0) (hu0 : u ≠ 0) (hv : v ∈ DDsp σ w0) (ξ : Wp) :
    Integrable (fun x : Mt k r => ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2) ν ∧
    ∫ x, ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2 ∂ν =
      ‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u ∧
    ∫⁻ x, (‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖₊ : ℝ≥0∞) ^ 2 ∂ν =
      ENNReal.ofReal (‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u) := by
  obtain ⟨ε, lam, -, hds⟩ := hG.1
  exact normId_of_bd hG hGr hSg hPi hPs hM hS hu0 ha (Formalism.MainNotions.InverseNormDecayBounds.decDD hds ha hD u hu v hv)
    (Formalism.MainNotions.InverseNormDecayBounds.decDD hds ha hD v hv v hv) hGg hSS ξ

def DecInfAt (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ v0 : H, IsKFinHpk (k := k) (r := r) σ v0 → ∃ (C : ℝ) (Ws : List (List (Mx k r))),
    (∀ W ∈ Ws, ∀ X ∈ W, InLieHpk k r X) ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
      ‖⟪v0, σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖dsigW σ W w‖).sum * Formalism.FourierDecayAlt.B.gN x ^ (1 - a)

theorem decBd_of_decInf {σ : Mx k r → (H →L[ℂ] H)} {a : ℝ} (hI : DecInfAt σ a) {v0 w : H}
    (hv0 : IsKFinHpk (k := k) (r := r) σ v0) (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    DecBd σ (a - 1) v0 w := by
  obtain ⟨C, Ws, -, hC⟩ := hI v0 hv0
  refine ⟨C * (Ws.map fun W => ‖dsigW σ W w‖).sum, fun x hx => ?_⟩
  have h1 := hC w hw x hx
  rwa [show -(a - 1) = 1 - a by ring]

theorem normId_smDD {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG ν : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)}
    (hG : GHyp z π μW μN μG ν σ)
    (hGr : Cv.GrpF k r z) (hSg : Cv.SigU σ) (hPi : Cv.PiU z π) (hPs : Cv.PsiF k r z c) (hM : Cv.MeasF z π μW μN)
    (hS : SchurOn μG σ) {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hds : IsDSHpk k r ε lam σ) {w0 : H} (hw0 : IsLowUnitH k r ε lam σ w0) {a : ℝ} (ha : 1 ≤ a)
    (hD : DiagonalMatrixCoefficientPowerDecay σ w0 a) (hI : DecInfAt σ a)
    (hGg : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-((a - 1) / 2))) μG)
    (hSS : Integrable (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-((a - 1) / 2))) (μW.prod μN))
    {u v : H} (hu : u ∈ smoothVecs (k := k) (r := r) σ) (hu0 : u ≠ 0) (hv : v ∈ DDsp σ w0) (ξ : Wp) :
    Integrable (fun x : Mt k r => ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2) ν ∧
    ∫ x, ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2 ∂ν =
      ‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u ∧
    ∫⁻ x, (‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖₊ : ℝ≥0∞) ^ 2 ∂ν =
      ENNReal.ofReal (‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u) := by
  have hb : 0 ≤ a - 1 := by linarith
  have hw0K := Formalism.MainNotions.DoubleDerivativeSmoothness.kfinHpk_of_lowUnitH hw0
  have huv : DecBd σ (a - 1) v u := decBd_DD_left hds hSg hb (decBd_of_decInf hI hw0K hu) v hv
  have hvv : DecBd σ (a - 1) v v :=
    decBd_mono (by linarith) (Formalism.MainNotions.InverseNormDecayBounds.decDD hds (by linarith) hD v hv v hv)
  exact normId_of_bd hG hGr hSg hPi hPs hM hS hu0 hb huv hvv hGg hSS ξ

theorem normId_smK {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG ν : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)}
    (hG : GHyp z π μW μN μG ν σ)
    (hGr : Cv.GrpF k r z) (hSg : Cv.SigU σ) (hPi : Cv.PiU z π) (hPs : Cv.PsiF k r z c) (hM : Cv.MeasF z π μW μN)
    (hS : SchurOn μG σ) {a : ℝ} (ha : 1 ≤ a) (hI : DecInfAt σ a)
    (hGg : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-((a - 1) / 2))) μG)
    (hSS : Integrable (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-((a - 1) / 2))) (μW.prod μN))
    {u v : H} (hu : u ∈ smoothVecs (k := k) (r := r) σ) (hu0 : u ≠ 0)
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (hvK : IsKFinHpk (k := k) (r := r) σ v) (ξ : Wp) :
    Integrable (fun x : Mt k r => ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2) ν ∧
    ∫ x, ‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖ ^ 2 ∂ν =
      ‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u ∧
    ∫⁻ x, (‖be z c π μW μN σ (σ (Matrix.of x) u) v ξ‖₊ : ℝ≥0∞) ^ 2 ∂ν =
      ENNReal.ofReal (‖u‖ ^ 2 * (⟪be z c π μW μN σ v v ξ, ξ⟫_ℂ).re / fdegH μG σ u) :=
  normId_of_bd hG hGr hSg hPi hPs hM hS hu0 (by linarith) (decBd_of_decInf hI hvK hu) (decBd_of_decInf hI hvK hv) hGg hSS ξ

end PI.WBL.NIS
