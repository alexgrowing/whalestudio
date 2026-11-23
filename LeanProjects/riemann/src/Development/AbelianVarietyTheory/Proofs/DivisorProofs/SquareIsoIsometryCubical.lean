import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricDeterminedByCurvatureZeroSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormMulPullZeroSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicSmoothOnOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSqHolomorphicPluriharmonicStatement
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section
namespace GlobalTheory.SqIsoIsom

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def mulL (n : ℤ) : Pt E g →L[ℝ] Pt E g :=
  (ContinuousLinearMap.fst ℝ E (Fin g → ℂ)).prod ((n : ℝ) • ContinuousLinearMap.snd ℝ E (Fin g → ℂ))

theorem mulL_apply (n : ℤ) (P : Pt E g) : mulL n P = mulN n P := by
  simp [mulL, mulN, Int.cast_smul_eq_zsmul]

theorem mulN_eq (n : ℤ) : (mulN n : Pt E g → Pt E g) = mulL n := by
  funext P; exact (mulL_apply n P).symm

theorem fderiv_mulN (n : ℤ) (P : Pt E g) : fderiv ℝ (mulN n : Pt E g → Pt E g) P = mulL n := by
  rw [mulN_eq]; exact (mulL (E := E) (g := g) n).hasFDerivAt.fderiv

theorem per_zsmul (τ : Matrix (Fin g) (Fin g) ℂ) (n : ℤ) (l : Fl g) :
    per τ (n • l) = n • per τ l := by
  funext i
  simp [per, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_add, mul_assoc]

theorem mulN_transl (τ : E → Matrix (Fin g) (Fin g) ℂ) (n : ℤ) (l : Fl g) (P : Pt E g) :
    mulN n (transl τ l P) = transl τ (n • l) (mulN n P) := by
  simp only [mulN, transl, per_zsmul, smul_add]

end GlobalTheory.SqIsoIsom

namespace GlobalTheory.SqIsoIsom
variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem du_at {s : Set (Pt E g)} {u : Pt E g → ℝ} (hu : ContDiffOn ℝ 2 u s) (hs : IsOpen s)
    {Q : Pt E g} (hQ : Q ∈ s) : DifferentiableAt ℝ u Q :=
  (hu.differentiableOn (by norm_num)).differentiableAt (hs.mem_nhds hQ)

theorem dd_apply {s : Set (Pt E g)} {u : Pt E g → ℝ} (hu : ContDiffOn ℝ 2 u s) (hs : IsOpen s)
    {P : Pt E g} (hP : P ∈ s) (x : Pt E g) : DifferentiableAt ℝ (fun Q => fderiv ℝ u Q x) P := by
  have hd : DifferentiableOn ℝ (fderiv ℝ u) s :=
    (hu.fderiv_of_isOpen hs (m := 1) (by norm_num)).differentiableOn one_ne_zero
  exact ((hd P hP).differentiableAt (hs.mem_nhds hP)).clm_apply (differentiableAt_const x)

theorem ddc_lin {s : Set (Pt E g)} {u u₁ u₂ : Pt E g → ℝ} (c : ℝ) (hs : IsOpen s)
    (h1 : ContDiffOn ℝ 2 u₁ s) (h2 : ContDiffOn ℝ 2 u₂ s) (he : ∀ Q ∈ s, u Q = c * u₁ Q + u₂ Q) :
    ∀ P ∈ s, ∀ v w : Pt E g, ddc u P v w = c * ddc u₁ P v w + ddc u₂ P v w := by
  intro P hP v w
  have key : ∀ x, (fun Q => fderiv ℝ u Q x) =ᶠ[nhds P]
      fun Q => c * fderiv ℝ u₁ Q x + fderiv ℝ u₂ Q x := by
    intro x
    filter_upwards [hs.mem_nhds hP] with Q hQ
    have he' : u =ᶠ[nhds Q] fun Q => c * u₁ Q + u₂ Q := by
      filter_upwards [hs.mem_nhds hQ] with R hR using he R hR
    have hd : HasFDerivAt (fun Q => c * u₁ Q + u₂ Q)
        (c • fderiv ℝ u₁ Q + fderiv ℝ u₂ Q) Q :=
      ((du_at h1 hs hQ).hasFDerivAt.const_mul c).add (du_at h2 hs hQ).hasFDerivAt
    rw [he'.fderiv_eq, hd.fderiv]
    simp
  have e : ∀ x y, fderiv ℝ (fun Q => fderiv ℝ u Q x) P y =
      c * fderiv ℝ (fun Q => fderiv ℝ u₁ Q x) P y + fderiv ℝ (fun Q => fderiv ℝ u₂ Q x) P y := by
    intro x y
    have hd : HasFDerivAt (fun Q => c * fderiv ℝ u₁ Q x + fderiv ℝ u₂ Q x)
        (c • fderiv ℝ (fun Q => fderiv ℝ u₁ Q x) P + fderiv ℝ (fun Q => fderiv ℝ u₂ Q x) P) P :=
      ((dd_apply h1 hs hP x).hasFDerivAt.const_mul c).add (dd_apply h2 hs hP x).hasFDerivAt
    rw [(key x).fderiv_eq, hd.fderiv]
    simp
  simp only [ddc, e]
  ring

theorem ddc_comp_clm {s : Set (Pt E g)} {u : Pt E g → ℝ} (L : Pt E g →L[ℝ] Pt E g)
    (hLI : ∀ x, L (Complex.I • x) = Complex.I • L x) (hs : IsOpen s)
    (hmap : Set.MapsTo L s s) (hu : ContDiffOn ℝ 2 u s) :
    ∀ P ∈ s, ∀ v w : Pt E g, ddc (fun Q => u (L Q)) P v w = ddc u (L P) (L v) (L w) := by
  intro P hP v w
  have key : ∀ x, (fun Q => fderiv ℝ (fun Q => u (L Q)) Q (Complex.I • x)) =ᶠ[nhds P]
      fun Q => fderiv ℝ u (L Q) (Complex.I • L x) := by
    intro x
    filter_upwards [hs.mem_nhds hP] with Q hQ
    have hd : HasFDerivAt (fun Q => u (L Q)) ((fderiv ℝ u (L Q)).comp L) Q :=
      (du_at hu hs (hmap hQ)).hasFDerivAt.comp Q L.hasFDerivAt
    rw [hd.fderiv, ContinuousLinearMap.comp_apply, hLI]
  have e : ∀ x y, fderiv ℝ (fun Q => fderiv ℝ (fun Q => u (L Q)) Q (Complex.I • x)) P y =
      fderiv ℝ (fun R => fderiv ℝ u R (Complex.I • L x)) (L P) (L y) := by
    intro x y
    rw [(key x).fderiv_eq]
    have hd : HasFDerivAt (fun Q => fderiv ℝ u (L Q) (Complex.I • L x))
        ((fderiv ℝ (fun R => fderiv ℝ u R (Complex.I • L x)) (L P)).comp L) P :=
      (dd_apply hu hs (hmap hP) _).hasFDerivAt.comp P L.hasFDerivAt
    rw [hd.fderiv]
    rfl
  simp only [ddc, e]

theorem ddc_comp_mulN {s : Set (Pt E g)} {u : Pt E g → ℝ} (n : ℤ) (hs : IsOpen s)
    (hmap : Set.MapsTo (mulN n) s s) (hu : ContDiffOn ℝ 2 u s) :
    ∀ P ∈ s, ∀ v w : Pt E g, ddc (fun Q => u (mulN n Q)) P v w =
      ddc u (mulN n P) (mulN n v) (mulN n w) := by
  rw [mulN_eq] at hmap ⊢
  refine ddc_comp_clm (mulL n) (fun x => ?_) hs hmap hu
  rw [mulL_apply, mulL_apply]
  exact Prod.ext rfl (smul_comm _ _ _)

end GlobalTheory.SqIsoIsom

namespace GlobalTheory.SqIsoIsom
variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem contDiffOn_of_holo [FiniteDimensional ℂ E] {s : Set (Pt E g)} {φ : Pt E g → ℂ}
    (hs : IsOpen s) (hφ : DifferentiableOn ℂ φ s) : ContDiffOn ℝ ∞ φ s :=
  GlobalTheory.T.holomorphic_smooth_on_open hs hφ

theorem ddc_log_normSq [FiniteDimensional ℂ E] {s : Set (Pt E g)} {φ : Pt E g → ℂ}
    (hs : IsOpen s) (hφ : DifferentiableOn ℂ φ s) (h0 : ∀ P ∈ s, φ P ≠ 0) :
    ∀ P ∈ s, ∀ v w : Pt E g, ddc (fun Q => Real.log (‖φ Q‖ ^ 2)) P v w = 0 :=
  GlobalTheory.T.log_norm_sq_holomorphic_pluriharmonic hs hφ h0

end GlobalTheory.SqIsoIsom

namespace GlobalTheory.SqIsoIsom

theorem sqIso_isometry : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (r : E → ℂ), IsFactor B τ (stdLat g) j → (∃ ι, IsBundleIso B τ (stdLat g) (mulPullFactor (-1) j) j ι) → IsRigidification B r → InducesPolarisation B τ (stdLat g) j → ∀ n : ℤ, ∀ h φ, IsCubicalMetric B τ j r h → IsSquareIso B τ j r n φ → IsIsometry B (fun P => h (mulN n P)) (fun P => h P ^ (n.natAbs ^ 2)) φ := by
  intro g E _ _ _ B τ hτ j r hj hsym hr hpol n h φ hh hφ
  have hB : IsOpen B := hτ.1
  have hcov : IsOpen (cov B g) := hB.prod isOpen_univ
  have hmap : Set.MapsTo (mulN n) (cov B g) (cov B g) := fun P hP => ⟨hP.1, trivial⟩
  set N := n.natAbs ^ 2 with hN
  obtain ⟨⟨hsm, hpos, htr⟩, hch, hz⟩ := hh
  obtain ⟨⟨hφd, hφ0, hφtr⟩, hφz⟩ := hφ
  have hφs : ContDiffOn ℝ ∞ φ (cov B g) := contDiffOn_of_holo hcov hφd
  have hlogh : ContDiffOn ℝ ∞ (fun Q => Real.log (h Q)) (cov B g) :=
    hsm.log fun Q hQ => (hpos Q hQ).ne'
  have hnφ : ContDiffOn ℝ ∞ (fun Q => ‖φ Q‖ ^ 2) (cov B g) :=
    (contDiff_norm_sq ℝ).comp_contDiffOn hφs
  have hlogφ : ContDiffOn ℝ ∞ (fun Q => Real.log (‖φ Q‖ ^ 2)) (cov B g) :=
    hnφ.log fun Q hQ => pow_ne_zero _ (norm_ne_zero_iff.2 (hφ0 Q hQ))
  have M1 : IsMetric B τ (stdLat g) (mulPullFactor n j) (fun P => h (mulN n P)) := by
    refine ⟨?_, fun P hP => hpos _ (hmap hP), fun l hl P hP => ?_⟩
    · rw [mulN_eq]
      exact hsm.comp (mulL (E := E) (g := g) n).contDiff.contDiffOn (by rw [← mulN_eq]; exact hmap)
    · simp only [mulPullFactor]
      rw [mulN_transl]
      exact htr _ ((stdLat g).smul_mem n hl) _ (hmap hP)
  have M2 : IsMetric B τ (stdLat g) (mulPullFactor n j) (fun P => h P ^ N * ‖φ P‖ ^ 2) := by
    refine ⟨(hsm.pow N).mul hnφ, fun P hP => mul_pos (pow_pos (hpos P hP) N)
      (pow_pos (norm_pos_iff.2 (hφ0 P hP)) 2), fun l hl P hP => ?_⟩
    have e1 := congrArg (fun x : ℂ => ‖x‖) (hφtr l hl P hP)
    simp only [norm_mul, norm_pow] at e1
    have e2 := htr l hl P hP
    show h (transl τ l P) ^ N * ‖φ (transl τ l P)‖ ^ 2 * ‖mulPullFactor n j l P‖ ^ 2 = h P ^ N * ‖φ P‖ ^ 2
    rw [← e2]
    calc h (transl τ l P) ^ N * ‖φ (transl τ l P)‖ ^ 2 * ‖mulPullFactor n j l P‖ ^ 2
        = h (transl τ l P) ^ N * (‖φ (transl τ l P)‖ * ‖mulPullFactor n j l P‖) ^ 2 := by ring
      _ = h (transl τ l P) ^ N * (‖j l P‖ ^ N * ‖φ P‖) ^ 2 := by rw [e1]
      _ = (h (transl τ l P) * ‖j l P‖ ^ 2) ^ N * ‖φ P‖ ^ 2 := by ring
  have hlin : ∀ Q ∈ cov B g, Real.log (h Q ^ N * ‖φ Q‖ ^ 2) =
      (N : ℝ) * Real.log (h Q) + Real.log (‖φ Q‖ ^ 2) := by
    intro Q hQ
    rw [Real.log_mul (pow_ne_zero _ (hpos Q hQ).ne')
      (pow_ne_zero _ (norm_ne_zero_iff.2 (hφ0 Q hQ))), Real.log_pow]
  have D : ∀ P ∈ cov B g, ∀ v w : Pt E g, ddc (fun Q => Real.log (h (mulN n Q))) P v w =
      ddc (fun Q => Real.log (h Q ^ N * ‖φ Q‖ ^ 2)) P v w := by
    intro P hP v w
    have h2le : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    rw [ddc_comp_mulN (u := fun Q => Real.log (h Q)) n hcov hmap (hlogh.of_le h2le) P hP v w,
      ddc_lin (N : ℝ) hcov (hlogh.of_le h2le) (hlogφ.of_le h2le) hlin P hP v w,
      ddc_log_normSq hcov hφd hφ0 P hP v w]
    have c1 := hch (mulN n P) (hmap hP) (mulN n v) (mulN n w)
    have c2 := hch P hP v w
    have hp := (GlobalTheory.T.flat_form_mul_pull_zero_section hτ).1 n P hP
    have hp2 : om0 τ (mulN n P) ![mulN n v, mulN n w] = (n : ℝ) ^ 2 * om0 τ P ![v, w] := by
      have := congrArg (fun α : Form2 E g => α ![v, w]) hp
      simp only [pull, fderiv_mulN, ContinuousAlternatingMap.compContinuousLinearMap_apply,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul] at this
      have hv : (⇑(mulL (E := E) (g := g) n) ∘ ![v, w]) = ![mulN n v, mulN n w] := by
        funext i
        fin_cases i <;> simp [mulL_apply]
      rw [hv] at this
      exact this
    have hNr : ((N : ℕ) : ℝ) = (n : ℝ) ^ 2 := by rw [hN, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [hNr]
    linear_combination (-1 : ℝ) * c1 - hp2 + (n : ℝ) ^ 2 * c2
  have Z : ∀ b ∈ B, h (mulN n (zeroSec g b)) = h (zeroSec g b) ^ N * ‖φ (zeroSec g b)‖ ^ 2 := by
    intro b hb
    have e0 : mulN n (zeroSec g b) = (zeroSec g b : Pt E g) := by simp [mulN, zeroSec]
    rw [e0]
    have hzb := hz b hb
    have hφb := congrArg (fun x : ℂ => ‖x‖ ^ 2) (hφz b hb)
    simp only [norm_mul, norm_pow, mul_pow] at hφb
    have hr0 : ‖r b‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hr.2 b hb))
    apply mul_right_cancel₀ hr0
    calc h (zeroSec g b) * ‖r b‖ ^ 2 = 1 := hzb
      _ = (h (zeroSec g b) * ‖r b‖ ^ 2) ^ N := by rw [hzb, one_pow]
      _ = h (zeroSec g b) ^ N * (‖φ (zeroSec g b)‖ ^ 2 * ‖r b‖ ^ 2) := by
          rw [hφb, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 N]
      _ = _ := by ring
  intro P hP
  exact (GlobalTheory.T.metric_determined_by_curvature_zero_section hτ (mulPullFactor n j) _ _ M1 M2 D Z hP).symm

end GlobalTheory.SqIsoIsom
