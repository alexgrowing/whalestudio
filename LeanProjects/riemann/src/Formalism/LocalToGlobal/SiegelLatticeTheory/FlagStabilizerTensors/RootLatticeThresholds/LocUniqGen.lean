import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.QuotRaw
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ProductDecompositionHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.HaarWN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WFLStepsLocHNProps

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.QuantumDeterminants
open scoped InnerProductSpace ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.WuDec

section Gen

open Classical

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem toUJ_eq {M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε)
    (x : Formalism.REAL.UJ ε) (h : M = uMat x) : toUJ M hM = x := by
  apply Subtype.ext
  apply Units.ext
  change uMat (toUJ M hM) = uMat x
  rw [uMat_toUJ, h]

variable {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ}
  {z0 : Fin (2 * r + k + 1) → ℂ} {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem gam_cond (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ UH (Hpk k r)) :
    (Qm e f wf z0 * m * B0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * m * B0) = Formalism.REAL.Jm ε := by
  have hm' : mᴴ * Hpk k r * m = Hpk k r := hm
  have key : (Qm e f wf z0 * m * B0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * m * B0)
      = B0ᴴ * (mᴴ * ((Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * Qm e f wf z0) * m) * B0 := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [key, gramQ hF, hm', hCP.BHB]

def gam (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hm : m ∈ UH (Hpk k r)) : Formalism.REAL.UJ ε :=
  toUJ _ (gam_cond hF hCP hm)

theorem cM_gam (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hm : m ∈ UH (Hpk k r)) :
    (Matrix.of (cM (Qi ε e f wf z0) P0 (gam hF hCP m hm)) : Matrix _ _ ℂ) = m := by
  have h1 : uMat (gam hF hCP m hm) = Qm e f wf z0 * m * B0 := uMat_toUJ _ _
  change (Qi ε e f wf z0 * uMat (gam hF hCP m hm) * P0 : Matrix _ _ ℂ) = m
  rw [h1]
  calc Qi ε e f wf z0 * (Qm e f wf z0 * m * B0) * P0
      = (Qi ε e f wf z0 * Qm e f wf z0) * m * (B0 * P0) := by simp only [Matrix.mul_assoc]
    _ = m := by rw [Qi_mul_Qm hF, hCP.BP, Matrix.one_mul, Matrix.mul_one]

theorem gam_cM (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) (x : Formalism.REAL.UJ ε)
    (hm : (Matrix.of (cM (Qi ε e f wf z0) P0 x) : Matrix _ _ ℂ) ∈ UH (Hpk k r)) :
    gam hF hCP _ hm = x := by
  unfold gam
  apply toUJ_eq
  change Qm e f wf z0 * (Qi ε e f wf z0 * uMat x * P0) * B0 = uMat x
  calc Qm e f wf z0 * (Qi ε e f wf z0 * uMat x * P0) * B0
      = (Qm e f wf z0 * Qi ε e f wf z0) * uMat x * (P0 * B0) := by simp only [Matrix.mul_assoc]
    _ = uMat x := by rw [Qm_mul_Qi hF, hCP.PB, Matrix.one_mul, Matrix.mul_one]

def WB {V : Type} [Zero V] (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) (W : Formalism.REAL.UJ ε → V)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : V :=
  if hm : m ∈ UH (Hpk k r) then W (gam hF hCP m hm) else 0

theorem WB_cM {V : Type} [Zero V] (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) (W : Formalism.REAL.UJ ε → V)
    (x : Formalism.REAL.UJ ε) : WB hF hCP W (Matrix.of (cM (Qi ε e f wf z0) P0 x)) = W x := by
  have hmem : (Matrix.of (cM (Qi ε e f wf z0) P0 x) : Matrix _ _ ℂ) ∈ UH (Hpk k r) := by
    have hx : (uMat x)ᴴ * Formalism.REAL.Jm ε * uMat x = Formalism.REAL.Jm ε := uMat_mem x
    have hQ : Qm e f wf z0 * Qi ε e f wf z0 = 1 := Qm_mul_Qi hF
    change (Qi ε e f wf z0 * uMat x * P0)ᴴ * Hpk k r * (Qi ε e f wf z0 * uMat x * P0) = Hpk k r
    calc (Qi ε e f wf z0 * uMat x * P0)ᴴ * Hpk k r * (Qi ε e f wf z0 * uMat x * P0)
        = P0ᴴ * ((uMat x)ᴴ * ((Qm e f wf z0 * Qi ε e f wf z0)ᴴ * Formalism.REAL.Jm ε *
            (Qm e f wf z0 * Qi ε e f wf z0)) * uMat x) * P0 := by
          rw [← gramQ hF]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = P0ᴴ * Formalism.REAL.Jm ε * P0 := by
          rw [hQ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hx]
      _ = Hpk k r := hCP.cay
  unfold WB
  rw [dif_pos hmem, gam_cM]

end Gen

section Trans

open Classical

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
  {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ}
  {z0 : Fin (2 * r + k + 1) → ℂ} {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem continuous_gam (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) :
    Continuous (fun p : UH (Hpk k r) => gam hF hCP p.1 p.2) := by
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · have e : ∀ p : UH (Hpk k r), (((gam hF hCP p.1 p.2 : Formalism.REAL.UJ ε) :
        (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix _ _ ℂ)
          = Qm e f wf z0 * p.1 * B0 := fun p => uMat_toUJ _ _
    simp only [Function.comp_def, e]
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  · have hinv : ∀ p : UH (Hpk k r), (((((gam hF hCP p.1 p.2 : Formalism.REAL.UJ ε) :
        (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ))⁻¹ :
        (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix _ _ ℂ)
          = Formalism.REAL.Jm ε * (Qm e f wf z0 * p.1 * B0)ᴴ * Formalism.REAL.Jm ε := fun p => rfl
    refine Continuous.congr (f := fun p : UH (Hpk k r) =>
      Formalism.REAL.Jm ε * (Qm e f wf z0 * p.1 * B0)ᴴ * Formalism.REAL.Jm ε) ?_ ?_
    · exact (continuous_const.matrix_mul
        ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).matrix_conjTranspose).matrix_mul
        continuous_const
    · intro p
      exact (hinv p).symm

theorem WB_continuousOn {V : Type} [TopologicalSpace V] [Zero V] (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0)
    {W : Formalism.REAL.UJ ε → V} (hW : Continuous W) : ContinuousOn (WB hF hCP W) (UH (Hpk k r)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hr : ∀ p : UH (Hpk k r), WB hF hCP W p.1 = W (gam hF hCP p.1 p.2) := by
    intro p
    unfold WB
    rw [dif_pos p.2]
  have hc : Continuous (fun p : UH (Hpk k r) => WB hF hCP W p.1) := by
    have hf : (fun p : UH (Hpk k r) => WB hF hCP W p.1) = fun p => W (gam hF hCP p.1 p.2) := funext hr
    rw [hf]
    exact hW.comp (continuous_gam hF hCP)
  exact hc

end Trans

section TransEq

open Classical

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
  {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ}
  {z0 : Fin (2 * r + k + 1) → ℂ} {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem cM_eq_of (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hm : m ∈ UH (Hpk k r)) : m = (Matrix.of (cM (Qi ε e f wf z0) P0 (gam hF hCP m hm)) : Matrix _ _ ℂ) := (cM_gam hF hCP m hm).symm

theorem WB_equiv (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) {zB z : Fin (2 * r + k + 1) → ℂ}
    (hz : (Qm e f wf z0) *ᵥ zB = z) {gg : ℕ} (hgg : 0 < gg) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {πl : Matrix (Fin k) (Fin k) ℂ → (V →L[ℂ] V)} {W : Formalism.REAL.UJ ε → V}
    (hWe : ∀ s x : Formalism.REAL.UJ ε, ∀ h ∈ UWset k r zB, ∀ m ∈ Nset k r,
      Qi ε e f wf z0 * uMat s * Qm e f wf z0 = h * m →
      W (s * x) = psiR ε gg e f z (uMat s) • piB ε e f wf z0 πl h (W x)) :
    IsSPsiEquiv zB (Formalism.QuantumDeterminants.psi k r zB ((4 * Real.pi / gg : ℝ) : ℂ)) (piB ε e f wf z0 πl) (WB hF hCP W) := by
  intro h hh m hm g hg
  have hhm : h * m ∈ UH (Hpk k r) := mem_UH_mul hh.1 hm.1
  set s : Formalism.REAL.UJ ε := toUJ (Qm e f wf z0 * (h * m) * Qi ε e f wf z0) (conjQ_UJ hF hhm) with hs
  set x := gam hF hCP g hg with hx
  have hus : uMat s = Qm e f wf z0 * (h * m) * Qi ε e f wf z0 := uMat_toUJ _ _
  have hsQ : Qi ε e f wf z0 * uMat s * Qm e f wf z0 = h * m := by rw [hus]; exact Qi_Qm_conj hF _
  have hsx : h * m * g = (Matrix.of (cM (Qi ε e f wf z0) P0 (s * x)) : Matrix _ _ ℂ) := by
    have hg' := cM_gam hF hCP g hg
    show h * m * g = Qi ε e f wf z0 * uMat (s * x) * P0
    rw [Formalism.L2.SG.WuDecayPf.uMat_mul', hus]
    conv_lhs => rw [← hg']
    show h * m * (Qi ε e f wf z0 * uMat x * P0) = _
    simp only [← Matrix.mul_assoc, Qi_mul_Qm hF, Matrix.one_mul]
  rw [hsx, WB_cM, cM_eq_of hF hCP g hg, WB_cM, hWe s x h hh m hm hsQ]
  congr 1
  rw [← psi_conj hF hz hgg (uMat s), hsQ, psiGen_UW_mul _ hh, Formalism.L2.SG.LitS.psi_eq_psiGen]

end TransEq

section TransRep

open Classical

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
  {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ}
  {z0 : Fin (2 * r + k + 1) → ℂ} {P0 B0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem WB_reprod (hF : IsFrameJ ε e f wf z0) (hCP : CayPair ε P0 B0) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] {W : Formalism.REAL.UJ ε → V}
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG ε) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG ε) = W x) :
    ∀ x' ∈ UH (Hpk k r),
      Integrable (fun g : Mt k r => eFun ((Formalism.REAL.muG ε).map (cM B0 P0)) (fun M => σ (P0 * M * B0)) w
          (Matrix.of g) • WB hF hCP W (x' * Matrix.of g)) ((Formalism.REAL.muG ε).map (cM B0 P0)) ∧
      rconv ((Formalism.REAL.muG ε).map (cM B0 P0)) (eFun ((Formalism.REAL.muG ε).map (cM B0 P0)) (fun M => σ (P0 * M * B0)) w)
        (WB hF hCP W) x' = WB hF hCP W x' := by
  intro x' hx'
  set x := gam hF hCP x' hx' with hxdef
  have hx'eq : (Matrix.of (cM (Qi ε e f wf z0) P0 x) : Matrix _ _ ℂ) = x' := cM_gam hF hCP x' hx'
  obtain ⟨hint, hval⟩ := hWr x
  have embG := cM_measEmb (ε := ε) (A := B0) (B := P0) (A' := P0) (B' := B0) hCP.PB hCP.PB
  have hfd := fdegH_map hCP σ w
  have hσg : ∀ g : Formalism.REAL.UJ ε, σ (P0 * (Matrix.of (cM B0 P0 g) : Matrix _ _ ℂ) * B0) = σ (uMat g) := by
    intro g
    show σ (P0 * (B0 * uMat g * P0) * B0) = σ (uMat g)
    congr 1; simp only [← Matrix.mul_assoc, hCP.PB, Matrix.one_mul]; rw [Matrix.mul_assoc, hCP.PB, Matrix.mul_one]
  have hprod : ∀ g : Formalism.REAL.UJ ε, (Matrix.of (cM (Qi ε e f wf z0) P0 x) : Matrix _ _ ℂ) *
      Matrix.of (cM B0 P0 g) = Matrix.of (cM (Qi ε e f wf z0) P0 (x * g)) := fun g => cMprod hCP _ x g
  have hpt : ∀ g : Formalism.REAL.UJ ε, eFun ((Formalism.REAL.muG ε).map (cM B0 P0))
      (fun M => σ (P0 * M * B0)) w (Matrix.of (cM B0 P0 g)) • WB hF hCP W (x' * Matrix.of (cM B0 P0 g)) =
      (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g) := by
    intro g
    simp only [eFun]
    rw [hfd, hσg, ← hx'eq, hprod, WB_cM]
  refine ⟨?_, ?_⟩
  · exact embG.integrable_map_iff.mpr (hint.congr (ae_of_all _ fun g => (hpt g).symm))
  · unfold rconv
    rw [embG.integral_map, integral_congr_ae (ae_of_all _ hpt), hval, ← hx'eq, WB_cM]

end TransRep

section Main

open Classical Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay

variable {k r : ℕ}

theorem isHaarOn_smul {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)} {μ : Measure (Mt k r)}
    (h : IsHaarOn S μ) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) : IsHaarOn S (c • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : c • μ = c.toNNReal • μ := by
      rw [ENNReal.smul_def, ENNReal.coe_toNNReal hct]
    rw [this]
    infer_instance
  · intro h0
    apply h2
    rw [← Measure.measure_univ_eq_zero] at h0 ⊢
    rw [Measure.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left hc0
  · rw [Measure.smul_apply, h3, smul_zero]
  · intro s hs
    rw [Measure.map_smul, h4 s hs]

theorem locUniq_gen (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : Formalism.L2.SG.LitS.BesselMultOne)
    (hB : BesselNVGap) (hCW : CoefWeightedLoc) (hWl : WlocExists)
    (hk : 1 ≤ k) (hke : Even k) {T : ℝ} (hT : 0 < T) {gg : ℕ} (hgg : 0 < gg)
    {e f : Fin r → Fin (2 * r + k + 1) → ℂ} {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z : Fin (2 * r + k + 1) → ℂ}
    (hF : IsFrameJ (eps48 k r) e f wf (z0v T z))
    {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (hu : Formalism.QuantumDeterminants.IsHCParam u)
    (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) (hI : InterlacingCondition k r u v b) (hH : HalfIntegralDifference k r u v b)
    (hGap : GapBig k r b) {h : ℝ} (hga : Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) (lam48 k r v b) h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hDS : IsDS (eps48 k r) (lam48 k r v b) σ)
    {w : H} (hw : IsLowUnit (eps48 k r) (lam48 k r v b) σ w)
    {Vl : Type} [NormedAddCommGroup Vl] [InnerProductSpace ℂ Vl] [FiniteDimensional ℂ Vl]
    {πl : Matrix (Fin k) (Fin k) ℂ → (Vl →L[ℂ] Vl)} (hπ : IsHCTypeU k u πl)
    {μS ν : Measure (Formalism.REAL.UJ (eps48 k r))} (hS : IsLocHaar (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T)) μS)
    (hQ : IsLocQuot μS ν)
    {W : Formalism.REAL.UJ (eps48 k r) → Vl} (hWc : Continuous W)
    (hWe : ∀ s x : Formalism.REAL.UJ (eps48 k r), ∀ h ∈ UWset k r (zBv k r T), ∀ m ∈ Nset k r,
      Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z) = h * m →
      W (s * x) = psiR (eps48 k r) gg e f z (uMat s) • piB (eps48 k r) e f wf (z0v T z) πl h (W x))
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG (eps48 k r)) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG (eps48 k r)) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG (eps48 k r)) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG (eps48 k r)) = W x)
    (hL0 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ 0) (hLt : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ ⊤) :
    (∫⁻ x, ‖W x‖ₑ * ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ∂ν
      < ⊤) ∧
    ∃ (α : Formalism.REAL.UJ (eps48 k r) → ℂ) (Ω : Set (Formalism.REAL.UJ (eps48 k r))) (a : ℝ), IsCompact Ω ∧ 1 ∈ Ω ∧
      Measurable α ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x, Integrable (fun g => α g • W (x * g)) (Formalism.REAL.muG (eps48 k r)) ∧
        ∫ g, α g • W (x * g) ∂(Formalism.REAL.muG (eps48 k r)) = W x := by
  obtain ⟨P0, hP0⟩ := Formalism.MainNotions.S.Inh.exists_isCayleyU_eps48 k r hk
  have hCP : CayPair (eps48 k r) P0 (Hpk k r * P0ᴴ * Formalism.REAL.Jm (eps48 k r)) := ⟨hP0.1.2, rfl⟩
  generalize hB0 : Hpk k r * P0ᴴ * Formalism.REAL.Jm (eps48 k r) = B0 at hCP
  have hinv : P0⁻¹ = B0 := Matrix.inv_eq_left_inv hCP.BP
  have hσB1 : (fun g => (fun M => σ (P0 * M * B0)) (P0⁻¹ * g * P0)) = σ := by
    funext g
    simp only [hinv]
    congr 1
    simp only [← Matrix.mul_assoc, hCP.PB, Matrix.one_mul]
    rw [Matrix.mul_assoc, hCP.PB, Matrix.mul_one]
  have hDSB : IsDSHpk k r (eps48 k r) (lam48 k r v b) (fun M => σ (P0 * M * B0)) := ⟨P0, hP0, by rw [hσB1]; exact hDS⟩
  have hwB : IsLowUnitH k r (eps48 k r) (lam48 k r v b) (fun M => σ (P0 * M * B0)) w := ⟨P0, hP0, by rw [hσB1]; exact hw⟩
  have hcc0 : ((4 * Real.pi / gg : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 4 * Real.pi / gg := by positivity
    exact_mod_cast this.ne'
  have hTz : 0 < Tz k r (zBv k r T) := by rw [Tz_zB hT.le]; exact hT
  have hS48 : RealPlaceNumericalSetting k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) u v b :=
    ⟨hk, hke, inWb_zB T, hTz, fun _ => hcc0, hu, hl, hI, hH, hGap⟩
  have hπB := hcTypeW_piB hF hT.le hπ
  have hG := isHaarOn_G hCP
  have hSB := isHaarOn_S hF hS
  have hQB := isQuotMeas_B hF hCP hQ
  obtain ⟨μW, μN, hW, hN, hWfin, hNc⟩ := WlocSk.haar_measure_unipotent_nilradical k r (zBv k r T) (inWb_zB T) hTz
  obtain ⟨cS, hcS0, hcSt, hP⟩ := WlocSk.product_decomposition_holds k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) u v b H
    (fun M => σ (P0 * M * B0)) Vl (piB (eps48 k r) e f wf (z0v T z) πl) w _ _ _ μW μN
    ⟨hS48, hDSB, hπB, hwB, hG, hSB, hQB, hW, hN, hWfin, hNc⟩
  have hmuS : Formalism.MainNotions.S.muS μW μN =
      cS • (μS.map (cM (Qi (eps48 k r) e f wf (z0v T z)) (Qm e f wf (z0v T z)))) := hP
  have hQ' : IsQuotMeas ((Formalism.REAL.muG (eps48 k r)).map (cM B0 P0)) (Formalism.MainNotions.S.muS μW μN)
      (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) := by
    intro g hg
    rw [hQB g hg, hmuS]
    simp only [lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_const_mul' _ _ hcSt, ← mul_assoc, ENNReal.inv_mul_cancel hcS0 hcSt, one_mul]
  have hS' : IsHaarOn (Sset k r (zBv k r T)) (Formalism.MainNotions.S.muS μW μN) := by
    rw [hmuS]; exact isHaarOn_smul hSB hcS0 hcSt
  obtain ⟨W0, hc0, he0, hr0, -, hL20, hwt0, α, Ω, a, hΩc, h1Ω, hΩU, hαm, hαs, hαb, hαr⟩ :=
    hWl hB hCW k r (zBv k r T) _ u v b hS48 H _ hDSB Vl (piB (eps48 k r) e f wf (z0v T z) πl) hπB w hwB _ _ _
      hG hS' hQ'
  have hpsi : Formalism.QuantumDeterminants.psi k r (zBv k r T) ((4 * Real.pi / gg : ℝ) : ℂ) =
      psiGen k r (zBv k r T) (fun _ => ((4 * Real.pi / gg : ℝ) : ℂ)) := Formalism.L2.SG.LitS.psi_eq_psiGen _ _ _ _
  have he0' : IsSPsiEquiv (zBv k r T) (Formalism.QuantumDeterminants.psi k r (zBv k r T) ((4 * Real.pi / gg : ℝ) : ℂ))
      (piB (eps48 k r) e f wf (z0v T z) πl) W0 := by rw [hpsi]; exact he0
  have embX := cM_measEmb (ε := eps48 k r) (A := Qi (eps48 k r) e f wf (z0v T z)) (B := P0)
    (A' := Qm e f wf (z0v T z)) (B' := B0) (Qm_mul_Qi hF) hCP.PB
  have embG := cM_measEmb (ε := eps48 k r) (A := B0) (B := P0) (A' := P0) (B' := B0) hCP.PB hCP.PB
  have hXU : ∀ x : Formalism.REAL.UJ (eps48 k r),
      (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) ∈ UH (Hpk k r) := cX_mem_UH hF hCP

  have hl2eq : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) =
      cS⁻¹ * ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν := by
    unfold l2SG
    rw [lintegral_smul_measure, smul_eq_mul, embX.lintegral_map]
    congr 1
    refine lintegral_congr fun x => ?_
    show (‖WB hF hCP W (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖₊ : ℝ≥0∞) ^ 2 = ‖W x‖ₑ ^ 2
    rw [WB_cM]; rfl
  have hcSi0 : cS⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hcSt
  have hcSit : cS⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hcS0
  have hl2ne : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) ≠ 0 := by
    rw [hl2eq]; exact mul_ne_zero hcSi0 hL0
  have hl2lt : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) (WB hF hCP W) < ⊤ := by
    rw [hl2eq]; exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcSit) (lt_top_iff_ne_top.2 hLt)

  have hx0 : ∃ x0 ∈ UH (Hpk k r), W0 x0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : l2SG (cS⁻¹ • ν.map (cM (Qi (eps48 k r) e f wf (z0v T z)) P0)) W0 = 0 := by
      unfold l2SG
      rw [lintegral_smul_measure, smul_eq_mul, embX.lintegral_map]
      have hz0 : ∀ x : Formalism.REAL.UJ (eps48 k r),
          (‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖₊ : ℝ≥0∞) ^ 2 = 0 := by
        intro x; rw [hcon _ (hXU x)]; simp
      simp only [hz0, lintegral_zero, mul_zero]
    rw [hL20] at this
    exact one_ne_zero this
  obtain ⟨a', hprop⟩ := besselUniq_core hBW hM1 hl hDSB hga hok (inWb_zB T) hTz hcc0 hπB hwB (lowSmoothSK hDSB hwB)
    hG hW hN hQ' (WB_continuousOn hF hCP hWc) (WB_equiv hF hCP (Qm_zB hT z) hgg hWe) (WB_reprod hF hCP σ w hWr)
    hl2ne hl2lt hc0 he0' hr0 (by rw [hL20]; exact one_ne_zero) (by rw [hL20]; exact ENNReal.one_lt_top) hx0
  have hWeq : ∀ x : Formalism.REAL.UJ (eps48 k r),
      W x = a' • W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) := by
    intro x; rw [← hprop _ (hXU x), WB_cM]
  refine ⟨?_, ?_⟩
  ·
    have hc : 0 ≤ opn (Qm e f wf (z0v T z)) * opn B0 :=
      mul_nonneg (Formalism.L2.SG.WuDecayPf.opn_nonneg _) (Formalism.L2.SG.WuDecayPf.opn_nonneg _)
    have hN : 0 ≤ N1H k r := by unfold N1H; positivity
    set K : ℝ≥0∞ := ‖a'‖ₑ * ENNReal.ofReal ((opn (Qm e f wf (z0v T z)) * opn B0) ^ N1H k r) with hKdef
    have hpt : ∀ x, ‖W x‖ₑ *
        ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ≤
        K * (‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
          ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r)) := by
      intro x
      have h0 : 0 ≤ nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x :=
        Real.iInf_nonneg fun _ => Formalism.L2.SG.WuDecayPf.opn_nonneg _
      have h0' : 0 ≤ nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) :=
        Real.iInf_nonneg fun _ => Formalism.L2.SG.WuDecayPf.opn_nonneg _
      have hle := nuLoc_le hF hCP (zBv k r T) x
      rw [hWeq x, enorm_smul, hKdef]
      have h2 : ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r) ≤
          ENNReal.ofReal ((opn (Qm e f wf (z0v T z)) * opn B0) ^ N1H k r) *
            ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc _), ← Real.mul_rpow hc h0']
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h0 hle hN)
      calc ‖a'‖ₑ * ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
            ENNReal.ofReal (nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r)
          ≤ ‖a'‖ₑ * ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
            (ENNReal.ofReal ((opn (Qm e f wf (z0v T z)) * opn B0) ^ N1H k r) *
            ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r)) := by
            gcongr
        _ = _ := by ring
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)]
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top)) ?_
    have h3 := hwt0
    rw [lintegral_smul_measure, smul_eq_mul, embX.lintegral_map] at h3
    have h4 : ∫⁻ x, ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
        ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r) ∂ν =
        cS * (cS⁻¹ * ∫⁻ x, ‖W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x))‖ₑ *
        ENNReal.ofReal (nuH k r (zBv k r T) (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) ^ N1H k r) ∂ν) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hcS0 hcSt, one_mul]
    rw [h4]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcSt) h3
  ·
    refine ⟨fun g => α (cM B0 P0 g), cM B0 P0 ⁻¹' Ω, a, (cM_closedEmb hCP.PB hCP.PB).isCompact_preimage hΩc, ?_,
      hαm.comp embG.measurable, fun y hy => hαs _ hy, fun y => hαb _, ?_⟩
    · show Matrix.of (cM B0 P0 (1 : Formalism.REAL.UJ (eps48 k r))) ∈ Ω
      have : Matrix.of (cM B0 P0 (1 : Formalism.REAL.UJ (eps48 k r))) = (1 : Mat k r) := by
        show B0 * uMat 1 * P0 = 1; rw [uMat_one', Matrix.mul_one, hCP.BP]
      rw [this]; exact h1Ω
    · intro x
      obtain ⟨hint, hval⟩ := hαr _ (hXU x)
      have hint2 := embG.integrable_map_iff.mp hint
      have hprod : ∀ g : Formalism.REAL.UJ (eps48 k r), (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) *
          Matrix.of (cM B0 P0 g) = Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 (x * g)) :=
        fun g => cMprod hCP _ x g
      have hpt : ∀ g : Formalism.REAL.UJ (eps48 k r), α (cM B0 P0 g) • W (x * g) =
          a' • (α (Matrix.of (cM B0 P0 g)) • W0 ((Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) : Matrix _ _ ℂ) *
            Matrix.of (cM B0 P0 g))) := by
        intro g
        rw [hprod, hWeq, smul_comm]
        rfl
      refine ⟨(hint2.smul a').congr (ae_of_all _ fun g => (hpt g).symm), ?_⟩
      rw [integral_congr_ae (ae_of_all _ hpt), integral_smul]
      have h5 : ∫ g, α (Matrix.of (cM B0 P0 g)) • W0 ((Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x) :
          Matrix _ _ ℂ) * Matrix.of (cM B0 P0 g)) ∂(Formalism.REAL.muG (eps48 k r)) =
          W0 (Matrix.of (cM (Qi (eps48 k r) e f wf (z0v T z)) P0 x)) := by
        rw [← hval]
        unfold rconv
        rw [embG.integral_map]
      rw [h5, ← hWeq]

end Main

section Inst

open Classical Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay

theorem lowGap_of_gapHyp (D : Formalism.BasicNotions.D7) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (τ : D.what₂.Tau) :
    LowGapGe (16 * (D.R.r : ℝ) ^ 19) D.R.rS (Formalism.MainNotions.b48 D τ) := by
  obtain ⟨-, hgap⟩ := hG
  have hm := Formalism.MainNotions.two_rS_add_two D
  intro j hj
  have hj' : (Fin.cast hm j).1 + 1 < D.R.m := by simp; omega
  have hg := hgap τ (Fin.cast hm j) hj'
  have : Formalism.MainNotions.b48 D τ ⟨j.val + 1, hj⟩ - Formalism.MainNotions.b48 D τ j =
      (((D.hc τ).b ⟨(Fin.cast hm j).1 + 1, hj'⟩ - (D.hc τ).b (Fin.cast hm j) : ℚ) : ℝ) := by
    simp only [Formalism.MainNotions.b48]; push_cast; rfl
  rw [this]
  exact_mod_cast hg

theorem big_real (x y N : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hN : N = 2 * x + y + 1) (hN1 : 1801 ≤ N) :
    120 * N ^ 3 ≤ 16 * N ^ 19 ∧
    2 * (2 * (x ^ 2 + x + 1)) * ((2 * x + y) * (x * (x - 1) + 2 * x * (y + 1) + x ^ 2) + 4 * (y + x) * (x + 1)) +
      4 * (y + x) * (x + 1) + 3 ≤ 16 * N ^ 19 / (8 * Real.sqrt (2 * (x + 1))) ∧
    9 * (x + 1) * N ^ 2 + 3 * (4 * (y + x) * (x + 1)) + 3 ≤ 16 * N ^ 19 / (8 * Real.sqrt (2 * (x + 1))) := by
  have hN0 : 0 ≤ N := by linarith
  have hN1' : 1 ≤ N := by linarith
  have hxN : x ≤ N := by linarith
  have hyN : y ≤ N := by linarith
  have hx1 : x + 1 ≤ N := by linarith
  have hyx : y + x ≤ N := by linarith
  have hNN : N ≤ N * N := le_mul_of_one_le_right hN0 hN1'
  have eN2 : N ^ 2 = N * N := by ring
  have hNN2 : 1801 * N ≤ N * N := mul_le_mul_of_nonneg_right hN1 hN0
  have hs0 : 0 < Real.sqrt (2 * (x + 1)) := Real.sqrt_pos.mpr (by linarith)
  have hsN : Real.sqrt (2 * (x + 1)) ≤ N :=
    calc Real.sqrt (2 * (x + 1)) ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt (by rw [eN2]; linarith)
      _ = N := Real.sqrt_sq hN0
  have h12 : 1 ≤ N ^ 12 := one_le_pow₀ hN1'
  have h13 : 150 ≤ N ^ 13 := by
    calc (150 : ℝ) ≤ N * 1 := by linarith
      _ ≤ N * N ^ 12 := mul_le_mul_of_nonneg_left h12 hN0
      _ = N ^ 13 := by ring
  have h2 : 0 ≤ N ^ 2 := pow_nonneg hN0 2
  have h3 : 1 ≤ N ^ 3 := one_le_pow₀ hN1'
  have h3' : 0 ≤ N ^ 3 := pow_nonneg hN0 3
  have h5 : 1 ≤ N ^ 5 := one_le_pow₀ hN1'
  have h6 : 0 ≤ N ^ 6 := pow_nonneg hN0 6
  have h613 : 150 * N ^ 6 ≤ N ^ 13 * N ^ 6 := mul_le_mul_of_nonneg_right h13 h6
  have e19 : N ^ 13 * N ^ 6 = N ^ 19 := by ring
  have hR : 300 * N ^ 5 ≤ 16 * N ^ 19 / (8 * Real.sqrt (2 * (x + 1))) := by
    rw [le_div_iff₀ (by linarith)]
    have hm : 300 * N ^ 5 * (8 * Real.sqrt (2 * (x + 1))) ≤ 300 * N ^ 5 * (8 * N) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e1 : 300 * N ^ 5 * (8 * N) = 2400 * N ^ 6 := by ring
    linarith
  have hxx : x * x ≤ N * N := mul_le_mul hxN hxN hx hN0
  have hxy : x * y ≤ N * N := mul_le_mul hxN hyN hy hN0
  have hxy0 : 0 ≤ x * y := mul_nonneg hx hy
  have hxx0 : 0 ≤ x * x := mul_nonneg hx hx
  have hC1 : (y + x) * (x + 1) ≤ N * N := mul_le_mul hyx hx1 (by linarith) hN0
  have hC10 : 0 ≤ (y + x) * (x + 1) := mul_nonneg (by linarith) (by linarith)
  have hA : 2 * (2 * (x ^ 2 + x + 1)) ≤ 12 * N ^ 2 := by
    have ex : x ^ 2 = x * x := by ring
    rw [ex, eN2]
    linarith
  have hA0 : 0 ≤ 2 * (2 * (x ^ 2 + x + 1)) := by
    have ex : x ^ 2 = x * x := by ring
    rw [ex]
    linarith
  have eB : x * (x - 1) + 2 * x * (y + 1) + x ^ 2 = 2 * (x * x) + x + 2 * (x * y) := by ring
  have hB1 : x * (x - 1) + 2 * x * (y + 1) + x ^ 2 ≤ 6 * N ^ 2 := by
    rw [eB, eN2]
    linarith
  have hB0 : 0 ≤ x * (x - 1) + 2 * x * (y + 1) + x ^ 2 := by
    rw [eB]
    linarith
  have eC : 4 * (y + x) * (x + 1) = 4 * ((y + x) * (x + 1)) := by ring
  have hC : 4 * (y + x) * (x + 1) ≤ 4 * N ^ 2 := by
    rw [eC, eN2]
    linarith
  have hC0 : 0 ≤ 4 * (y + x) * (x + 1) := by
    rw [eC]
    linarith
  have hD : 2 * x + y ≤ N := by linarith
  have hD0 : 0 ≤ 2 * x + y := by linarith
  have hDB := mul_le_mul hD hB1 hB0 hN0
  have hDB0 := mul_nonneg hD0 hB0
  have h23 : N ^ 2 ≤ N ^ 2 * N := le_mul_of_one_le_right h2 hN1'
  have e3 : N * (6 * N ^ 2) = 6 * N ^ 3 := by ring
  have e3' : N ^ 2 * N = N ^ 3 := by ring
  have hB : (2 * x + y) * (x * (x - 1) + 2 * x * (y + 1) + x ^ 2) + 4 * (y + x) * (x + 1)
      ≤ 10 * N ^ 3 := by linarith
  have hB0' : 0 ≤ (2 * x + y) * (x * (x - 1) + 2 * x * (y + 1) + x ^ 2) + 4 * (y + x) * (x + 1) := by
    linarith
  have hAB := mul_le_mul hA hB hB0' (by linarith)
  have e5 : 12 * N ^ 2 * (10 * N ^ 3) = 120 * N ^ 5 := by ring
  have h25 : N ^ 2 ≤ N ^ 2 * N ^ 3 := le_mul_of_one_le_right h2 h3
  have e5' : N ^ 2 * N ^ 3 = N ^ 5 := by ring
  have h35 : N ^ 3 ≤ N ^ 3 * N ^ 2 := le_mul_of_one_le_right h3' (one_le_pow₀ hN1')
  have e5'' : N ^ 3 * N ^ 2 = N ^ 5 := by ring
  have h36 : N ^ 3 ≤ N ^ 3 * N ^ 3 := le_mul_of_one_le_right h3' h3
  have e6 : N ^ 3 * N ^ 3 = N ^ 6 := by ring
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · have hAB' : 2 * (2 * (x ^ 2 + x + 1)) *
        ((2 * x + y) * (x * (x - 1) + 2 * x * (y + 1) + x ^ 2) + 4 * (y + x) * (x + 1)) ≤ 120 * N ^ 5 := by
      linarith
    linarith
  · have h9 : (x + 1) * N ^ 2 ≤ N * N ^ 2 := mul_le_mul_of_nonneg_right hx1 h2
    have e9 : N * N ^ 2 = N ^ 3 := by ring
    have e9' : 9 * (x + 1) * N ^ 2 = 9 * ((x + 1) * N ^ 2) := by ring
    rw [e9']
    linarith

theorem gapOK_of_big (k r : ℕ) (hk : 1 ≤ k) (hN : 1801 ≤ 2 * r + k + 1) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (16 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 19) := by
  have hb := big_real (r : ℝ) (k : ℝ) ((2 * r + k + 1 : ℕ) : ℝ) (Nat.cast_nonneg r) (Nat.cast_nonneg k)
    (by push_cast; ring) (by exact_mod_cast hN)
  refine ⟨hk, hb.1, ?_, ?_⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.AG Formalism.FourierDecayAlt.ThreeDimData.aOf Formalism.FourierDecayAlt.ThreeDimData.dN
    have e1 : ((2 * r + k : ℕ) : ℝ) = 2 * (r : ℝ) + k := by push_cast; ring
    rw [e1]
    have := hb.2.1
    convert this using 2 <;> ring
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG Formalism.FourierDecayAlt.ThreeDimData.aOf
    have := hb.2.2
    convert this using 2 <;> ring

end Inst

section InstN

open Classical Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay

theorem locUniq_n (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : Formalism.L2.SG.LitS.BesselMultOne)
    (hB : BesselNVGap) (hCW : CoefWeightedLoc) (hWl : WlocExists) (hHN : LocHNProps)
    {k r n : ℕ} (hn : n = 2 * r + k + 1) (hk : 1 ≤ k) (hke : Even k) {T : ℝ} (hT : 0 < T) {gg : ℕ} (hgg : 0 < gg)
    (ε : Fin n → Bool) (hε : ∀ i, ε i = eps48 k r (Fin.cast hn i))
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (wf : Fin k → Fin n → ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0) (hzw : ∀ a, hJ ε z (wf a) = 0)
    {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ} {b : Fin (2 * r + 2) → ℝ} (hu : Formalism.QuantumDeterminants.IsHCParam u)
    (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) (hI : InterlacingCondition k r u v b) (hH : HalfIntegralDifference k r u v b)
    (hGap : GapBig k r b) {h : ℝ} (hga : Formalism.QuantumDeterminants.GapAtLeast (eps48 k r) (lam48 k r v b) h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (lam : Fin n → ℝ) (hlam : ∀ i, lam i = lam48 k r v b (Fin.cast hn i))
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hDS : IsDS ε lam σ) (w : H) (hw : IsLowUnit ε lam σ w)
    {Vl : Type} [NormedAddCommGroup Vl] [InnerProductSpace ℂ Vl] [FiniteDimensional ℂ Vl]
    (πl : Matrix (Fin k) (Fin k) ℂ → (Vl →L[ℂ] Vl)) (hπ : IsHCTypeU k u πl)
    (μS ν : Measure (Formalism.REAL.UJ ε))
    (hS : SigmaFinite μS ∧ μS ≠ 0 ∧
      μS {s | ∃ m ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z},
          s = m * h}ᶜ = 0 ∧
      ∀ s ∈ {s | ∃ m ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z},
          s = m * h}, μS.map (fun x => s * x) = μS)
    (hQ : ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
      ∫⁻ x, F x ∂(Formalism.REAL.muG ε) = ∫⁻ x, (∫⁻ s, F (s * x) ∂μS) ∂ν)
    (W : Formalism.REAL.UJ ε → Vl) (hWc : Continuous W)
    (hWe : ∀ m : Formalism.REAL.UJ ε, InN ε e z (uMat m) → ∀ h : Formalism.REAL.UJ ε,
      ((∀ a, uMat h *ᵥ e a = e a) ∧ (∀ a, uMat h *ᵥ f a = f a) ∧ uMat h *ᵥ z = z) → ∀ x,
      W (m * h * x) = psiR ε gg e f z (uMat (m * h)) • πl (fun a b => hJ ε (wf a) (uMat h *ᵥ wf b)) (W x))
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG ε) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG ε) = W x)
    (hL0 : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ 0) (hLt : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν ≠ ⊤) (N : ℝ) (hN : N ≤ N1H k r) :
    (∫⁻ x, ‖W x‖ₑ * ENNReal.ofReal
        ((⨅ t : {s : Formalism.REAL.UJ ε | InS e z (uMat s)}, opn (uMat ((t : Formalism.REAL.UJ ε) * x))) ^ N) ∂ν < ⊤) ∧
    ∃ (α : Formalism.REAL.UJ ε → ℂ) (Ω : Set (Formalism.REAL.UJ ε)) (a : ℝ), IsCompact Ω ∧ 1 ∈ Ω ∧
      Measurable α ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x, Integrable (fun g => α g • W (x * g)) (Formalism.REAL.muG ε) ∧
        ∫ g, α g • W (x * g) ∂(Formalism.REAL.muG ε) = W x := by
  subst hn
  have hε' : ε = eps48 k r := funext fun i => by rw [hε i]; rfl
  subst hε'
  have hlam' : lam = lam48 k r v b := funext fun i => by rw [hlam i]; rfl
  subst hlam'
  have hF := isFrameJ_of (ε := eps48 k r) e f z wf hT hee hff hef hez hfz hzz hww hew hfw hzw
  have hc : (((Real.sqrt T)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (Real.sqrt T)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hT).ne'
    exact_mod_cast this
  have hP := hHN k r (eps48 k r) e f wf (z0v T z) z _ hF hc rfl
  have heq : HNset (eps48 k r) e f wf (z0v T z) (zBv k r T) =
      {s | ∃ m ∈ {g : Formalism.REAL.UJ (eps48 k r) | InN (eps48 k r) e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ (eps48 k r) | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧
          uMat g *ᵥ z = z}, s = m * h} := Set.ext fun s => HNset_eq_NH hHN hT hF s
  have hS' : IsLocHaar (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T)) μS := by
    obtain ⟨h1, h2, h3, h4⟩ := hS
    exact ⟨h1, h2, by rw [heq]; exact h3, fun s hs => h4 s (heq ▸ hs)⟩
  have hz : (Qm e f wf (z0v T z)) *ᵥ (zBv k r T) = z := Qm_zB hT z
  have hzB0 := inWb_zB (k := k) (r := r) T
  have hWe' : ∀ s x : Formalism.REAL.UJ (eps48 k r), ∀ h' ∈ UWset k r (zBv k r T), ∀ m' ∈ Nset k r,
      Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z) = h' * m' →
      W (s * x) = psiR (eps48 k r) gg e f z (uMat s) • piB (eps48 k r) e f wf (z0v T z) πl h' (W x) := by
    intro s x h' hh' m' hm' hsm
    set sh : Formalism.REAL.UJ (eps48 k r) := toUJ (Qm e f wf (z0v T z) * h' * Qi (eps48 k r) e f wf (z0v T z))
      (conjQ_UJ hF hh'.1) with hsh
    set sm : Formalism.REAL.UJ (eps48 k r) := toUJ (Qm e f wf (z0v T z) * m' * Qi (eps48 k r) e f wf (z0v T z))
      (conjQ_UJ hF hm'.1) with hsm'
    have hush : uMat sh = Qm e f wf (z0v T z) * h' * Qi (eps48 k r) e f wf (z0v T z) := uMat_toUJ _ _
    have husm : uMat sm = Qm e f wf (z0v T z) * m' * Qi (eps48 k r) e f wf (z0v T z) := uMat_toUJ _ _
    have hfix : (∀ a, uMat sh *ᵥ e a = e a) ∧ (∀ a, uMat sh *ᵥ f a = f a) ∧ uMat sh *ᵥ z = z := by
      rw [hush]; exact rev_UW hF hz hh'
    have hNm : InN (eps48 k r) e z (uMat sm) := by rw [husm]; exact rev_N hF hz hzB0 hm'
    have hs_eq : s = sh * sm := by
      apply Subtype.ext; apply Units.ext
      show uMat s = uMat sh * uMat sm
      rw [hush, husm]
      have e1 : uMat s = Qm e f wf (z0v T z) * (Qi (eps48 k r) e f wf (z0v T z) * uMat s * Qm e f wf (z0v T z)) *
          Qi (eps48 k r) e f wf (z0v T z) := by
        simp only [← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul]
        rw [Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.mul_one]
      rw [e1, hsm]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (Qm e f wf (z0v T z) * h') (Qi (eps48 k r) e f wf (z0v T z)) (Qm e f wf (z0v T z)),
        Qi_mul_Qm hF, Matrix.mul_one]
    have hnn : InN (eps48 k r) e z (uMat (sh * sm * sh⁻¹)) := hP.2.2.2 sh hfix sm hNm
    have hs2 : s = sh * sm * sh⁻¹ * sh := by rw [hs_eq]; group
    rw [hs2, hWe _ hnn sh hfix x, ← hs2]
    unfold piB
    rw [hush]
  obtain ⟨hwt, α, Ω, a, hΩc, h1Ω, hαm, hαs, hαb, hαr⟩ := locUniq_gen hBW hM1 hB hCW hWl hk hke hT hgg hF hu hl hI
    hH hGap hga hok hDS hw hπ hS' hQ hWc hWe' hWr hL0 hLt
  refine ⟨?_, α, Ω, a, hΩc, h1Ω, hαm, hαs, hαb, hαr⟩
  have hn0 : 0 < 2 * r + k + 1 := by omega
  have hne1 : Nonempty {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)} := ⟨⟨1, inS_one⟩⟩
  have hne2 : Nonempty (HNset (eps48 k r) e f wf (z0v T z) (zBv k r T)) := by
    refine ⟨⟨1, ?_⟩⟩
    rw [heq]
    exact ⟨1, hP.2.2.1.1, 1, fix_one, (one_mul 1).symm⟩
  have hge1 : ∀ x, 1 ≤ ⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)},
      opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x)) := fun x =>
    le_ciInf fun t => Formalism.L2.SG.WuDecayPf.one_le_opn hn0 _
  have hle : ∀ x, (⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)},
      opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))) ≤
      nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x := by
    intro x
    refine le_ciInf fun t => ?_
    have ht : InS e z (uMat (t : Formalism.REAL.UJ (eps48 k r))) := inS_of_HNset hF hz hzB0 ⟨_, rfl⟩ t.2
    exact ciInf_le (f := fun t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)} =>
      opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x)))
      ⟨0, by rintro _ ⟨i, rfl⟩; exact Formalism.L2.SG.WuDecayPf.opn_nonneg _⟩ ⟨t, ht⟩
  have hN1 : 0 ≤ N1H k r := by unfold N1H; positivity
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hwt
  gcongr ‖W x‖ₑ * ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc (⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)}, opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))) ^ N
      ≤ (⨅ t : {s : Formalism.REAL.UJ (eps48 k r) | InS e z (uMat s)},
          opn (uMat ((t : Formalism.REAL.UJ (eps48 k r)) * x))) ^ N1H k r :=
        Real.rpow_le_rpow_of_exponent_le (hge1 x) hN
    _ ≤ nuLoc (e := e) (f := f) (wf := wf) (z0 := z0v T z) (zBv k r T) x ^ N1H k r :=
        Real.rpow_le_rpow (by linarith [hge1 x]) (hle x) hN1

end InstN

section Step

open Classical Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.WuDecay

theorem local_uniqueness_reduction : LocUniqStep := by
  intro hB hCW hWl hBW hM1 D hG X u μS νl C hQW v W hWc hWe hWr hL0 hLt
  obtain ⟨-, -, hloc, -⟩ := hQW
  obtain ⟨hSv, hQv⟩ := hloc v
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hN1801 : 1801 ≤ 2 * D.R.rS + D.R.k + 1 := by rw [dimS D]; exact hG.1
  have hT : (0 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have hgg : 0 < X.B.g := by
    rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have R := fun p q => Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    have := R (X.eX a) (X.eX b); rw [X.ee, map_zero] at this; exact this
  have hff : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0 := fun a b => by
    have := R (X.fY a) (X.fY b); rw [X.ff, map_zero] at this; exact this
  have hef : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 :=
    fun a b => by
      have := R (X.eX a) (X.fY b); rw [X.ef] at this; rw [show X.eR a = X.crd (X.eX a) from rfl,
        show X.fR b = X.crd (X.fY b) from rfl, this]; split_ifs <;> simp
  have hez : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 := fun a => by
    have := R (X.eX a) (X.zu u); rw [(X.zu_orth u a).1, map_zero] at this; exact this
  have hfz : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 := fun a => by
    have := R (X.fY a) (X.zu u); rw [(X.zu_orth u a).2, map_zero] at this; exact this
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(((D.mem u).A.T : ℝ) : ℂ) := by
    have := R (X.zu u) (X.zu u); rw [X.zu_norm, map_neg, map_natCast] at this
    rw [show X.zR u = X.crd (X.zu u) from rfl, this]; push_cast; rfl
  have hw1 := X.wfr_on u v
  have hew : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).1
  have hfw : ∀ c a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (X.wfr u v a) = 0 := fun c a => ((X.wfr_perp u v a).1 c).2
  have hzw : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0 := fun a => (X.wfr_perp u v a).2

  have hu := Formalism.MainNotions.uS_hc D u (X.pl v)
  have hl : Formalism.QuantumDeterminants.IsHCParam (lam48 D.R.k D.R.rS (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v))) := by
    rw [Formalism.MainNotions.lambda_highest_weight_eq]; exact Formalism.MainNotions.S.Inh.obj_isHCParam_lamSH D.R (D.hc (X.pl v))
  have hm := Formalism.MainNotions.two_rS_add_two D
  have hI : InterlacingCondition D.R.k D.R.rS (Formalism.MainNotions.S.uS D u (X.pl v)) (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v)) := by
    refine ⟨fun i => ?_, fun h => ?_⟩
    · have h1 := (D.hcW u (X.pl v)).u_gt_v i
      have h2 := (D.hcW u (X.pl v)).v_gt_u i
      rw [D.hcW_v u (X.pl v)] at h1 h2
      simp only [Formalism.MainNotions.v48, Formalism.MainNotions.S.uS]
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · have h1 := (D.hcW u (X.pl v)).u_last_gt h (by omega)
      rw [D.hcW_b u (X.pl v)] at h1
      simp only [Formalism.MainNotions.b48, Formalism.MainNotions.S.uS]
      have e : (Fin.cast hm ⟨0, by omega⟩ : Fin D.R.m) = ⟨0, by omega⟩ := rfl
      rw [e]
      exact_mod_cast h1
  have hH := Formalism.MainNotions.LeviCoordinates.halfInt_of_integrality _ _ _ _ _ hu hl
  have hGap := gapBig_of_gapHyp D hG (X.pl v)
  have hga := Formalism.MainNotions.gap_at_least_of_low_gap D.R.k D.R.rS (Formalism.MainNotions.v48 D (X.pl v)) (Formalism.MainNotions.b48 D (X.pl v)) _ hk hl.1
    (lowGap_of_gapHyp D hG (X.pl v))
  have hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (16 * (D.R.r : ℝ) ^ 19) := by
    have := gapOK_of_big D.R.k D.R.rS hk hN1801
    rwa [dimS D] at this

  have hNH : NHloc X u v = {s | ∃ m ∈ {g : Formalism.REAL.UJ (X.B.I.ε v) | InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
      (rv X.B.I v (X.zR u)) (uMat g)}, ∃ h ∈ {g : Formalism.REAL.UJ (X.B.I.ε v) |
        (∀ a, uMat g *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a)) ∧
        (∀ a, uMat g *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) ∧
        uMat g *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)}, s = m * h} := by
    unfold NHloc; rw [Hloc_eq]; rfl
  obtain ⟨h1, h2, h3, h4⟩ := hSv
  rw [hNH] at h3 h4

  have hWe' : ∀ m : Formalism.REAL.UJ (X.B.I.ε v), InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))
      (uMat m) → ∀ h : Formalism.REAL.UJ (X.B.I.ε v),
      ((∀ a, uMat h *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a)) ∧
        (∀ a, uMat h *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) ∧
        uMat h *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)) → ∀ x,
      W (m * h * x) = psiR (X.B.I.ε v) X.B.g (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
        (rv X.B.I v (X.zR u)) (uMat (m * h)) •
        X.piLoc u v (fun a b => hJ (X.B.I.ε v) (X.wfr u v a) (uMat h *ᵥ X.wfr u v b)) (W x) := by
    intro m hm h hh x
    have hh' : h ∈ Hloc X u v := by rw [Hloc_eq]; exact hh
    have hmat : matW X.B.I (X.wfr u v) v (single X v h) =
        fun a b => hJ (X.B.I.ε v) (X.wfr u v a) (uMat h *ᵥ X.wfr u v b) := by
      funext a b; simp [matW, single]
    rw [hWe m hm h hh' x, hmat]
    rfl
  have key := locUniq_n hBW hM1 hB hCW hWl Formalism.L2.SG.Pf.WFL.locHNProps_holds (hdim X) hk D.R.k_even hT hgg
    (X.B.I.ε v) (eps_cast X v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
    (rv X.B.I v (X.zR u)) (X.wfr u v) hee hff hef hez hfz hzz hw1 hew hfw hzw hu hl hI hH hGap hga hok
    (X.B.lam v) (lam_cast X v) (X.B.σ v) (X.ds v) (X.B.w v) (X.low v) (X.piLoc u v) (X.piLoc_type u v)
    (μS v) (νl v) ⟨h1, h2, h3, h4⟩ hQv W hWc hWe' hWr hL0 hLt (N1 X) (first_count_le_log X)
  exact key

end Step

end Formalism.L2.SG.Pf.WuDec
