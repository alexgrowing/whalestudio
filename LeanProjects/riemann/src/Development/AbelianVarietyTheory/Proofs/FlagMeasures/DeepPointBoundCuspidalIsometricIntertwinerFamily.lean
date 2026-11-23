import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DeepKernelBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionExponents
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentOrbitCover
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HalfTruncatedLeastLatticeSizeLeUnipotentNeighbou
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesStepBoundOfCountingHypothesesStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.DeepFamilyGap

theorem one_mem_NA (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) : (1 : I.GA) ∈ I.NA W := by
  unfold AutInst.NA
  refine ⟨fun v => ?_, ?_⟩
  · have hdet : IsUnit (I.P v).det := by
      first
      | exact (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
      | exact I.P_unit v
    have hg : I.P v * uMat ((1 : I.GA).1 v) * (I.P v)⁻¹ = 1 := by
      rw [show uMat ((1 : I.GA).1 v) = 1 from rfl, mul_one]
      exact Matrix.mul_nonsing_inv _ hdet
    rw [hg]
    unfold AutInst.InUnipRad
    simp
    intro x _
    unfold Formalism.UG.hform
    simp
  · have hf : I.fmat (1 : I.GA).2 = 1 := by
      first
      | rfl
      | simp
      | exact map_one _
    rw [hf]
    unfold AutInst.InUnipRad
    simp
    intro x _
    unfold Formalism.UG.hform
    simp

theorem self_mem_omega (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) {ρ : ℝ} (h : 0 ≤ ρ) :
    x ∈ omega I x W ρ := by
  refine ⟨rfl, fun _ => 0, fun _ => 0, fun v => ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (I.ε v)).zero_mem,
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (I.ε v)).zero_mem⟩, ?_, fun v => by simp, fun s t => ⟨1, ?_, fun v => ?_⟩⟩
  · simpa [GlobalTheory.SobolevBound.hs_eq_trace] using h
  · exact one_mem_NA I W
  · rw [smul_zero, smul_zero, NormedSpace.exp_zero, mul_one, mul_one]
    exact one_mul _

theorem beP_nonneg (n : ℕ) (b : ℝ) (P : ℕ) : 0 ≤ beP n b P := by
  unfold beP
  positivity

theorem monotone₂ (n : ℕ) (b : ℝ) {P Q : ℕ} (h : P ≤ Q) : beP n b P ≤ beP n b Q := by
  unfold beP
  have : (P : ℝ) ≤ Q := by exact_mod_cast h
  linarith

theorem iterate (B : RowsAut) (b ρ M β : ℝ) (P₀ : ℕ) (D : ℕ)
    (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA)
    (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (hg : 1 ≤ B.g) (hW : B.I.IsIsot W)
    (hcov : ∀ ν : B.I.Ginf, ((ν, 1) : B.I.GA) ∈ B.I.NA W → ∃ γ ∈ B.I.GFset, ∃ k ∈ B.I.Kg B.g,
      ∃ y ∈ omega B.I x W ρ, ((ν, 1) : B.I.GA) * x = γ * y * (1, k))
    (hS : ∀ P, StepBoundAt B b P) (hR : ∀ i, IsReps B (T i) (Fr i))
    (hC : ∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hβ : beP B.I.n b P₀ ≤ β)
    (h0 : ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P₀, ‖vv B Fr u y‖ ≤ M * ‖u‖) :
    ∀ k P : ℕ, P + k = P₀ → ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P,
      ‖vv B Fr u y‖ ≤ (2 * ρ * Real.sqrt B.I.f * β) ^ k * M * ‖u‖ := by
  have hβ0 : 0 ≤ β := le_trans (beP_nonneg _ _ _) hβ
  have hc0 : 0 ≤ 2 * ρ * Real.sqrt B.I.f * β :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ) (Real.sqrt_nonneg _)) hβ0
  intro k
  induction k with
  | zero =>
    intro P hP y hy u hu
    have hPP : P = P₀ := by simpa using hP
    subst hPP
    simpa using h0 y hy u hu
  | succ k ih =>
    intro P hP y hy u hu
    have hP' : (P + 1) + k = P₀ := by omega
    have hM' : 0 ≤ (2 * ρ * Real.sqrt B.I.f * β) ^ k * M := mul_nonneg (pow_nonneg hc0 _) hM
    have key := GlobalTheory.DeepStep.step_bound B b ρ ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) P D T Fr x W hg hW
      hcov (hS P) hR hC hM' (ih (P + 1) hP') y hy u hu
    have hle : beP B.I.n b P ≤ β := le_trans (monotone₂ _ _ (by omega : P ≤ P₀)) hβ
    calc ‖vv B Fr u y‖
        ≤ 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) * ‖u‖ := key
      _ ≤ 2 * ρ * Real.sqrt B.I.f * β * ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) * ‖u‖ := by
          gcongr
      _ = (2 * ρ * Real.sqrt B.I.f * β) ^ (k + 1) * M * ‖u‖ := by ring

theorem mult_le {n τ t : ℝ} (hn : 1 ≤ n) (hτ : 0 < τ) (hτ1 : τ < 1 / 2) (ht : τ / 2 ≤ t) :
    1 + 4 * Real.sqrt n / t ^ 2 ≤ 17 * Real.sqrt n / τ ^ 2 := by
  have hs : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hn
  have ht0 : 0 < t := by linarith
  have hτt : τ ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have h1 : 4 * Real.sqrt n / t ^ 2 ≤ 16 * Real.sqrt n / τ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : 1 ≤ Real.sqrt n / τ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : 17 * Real.sqrt n / τ ^ 2 = 16 * Real.sqrt n / τ ^ 2 + Real.sqrt n / τ ^ 2 := by ring
  linarith

theorem deep_bound_family : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ v, IsGauge (B.I.ε v) (c v)) → least B.I x < tauStar B q b → (∀ i, IsReps B (T i) (Fr i)) → (∀ i u, ‖T i u‖ = ‖u‖) → (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) → ‖vv B Fr (B.tens B.w) x‖ ^ 2 ≤ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal := by
  intro B Cg n₀ d p q b c x D T Fr hn₀ hq hCH hc hτ hR hiso hcusp
  obtain ⟨hDS, -, hn₀n, hq2, -, -, hb2, -, -, hg, -⟩ := id hCH
  obtain ⟨-, hrd, hf, -, -, -, hrk, -, -, -, -, htau, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn₀ hCH
  obtain ⟨htau2, hb19⟩ := htau hq
  have hn8 : 8 ≤ B.I.n := le_trans hn₀ hn₀n
  have hn1 : 1 ≤ B.I.n := by omega
  have hτpos : 0 < least B.I x :=
    ((GlobalTheory.CountSteps.steps B.I x 1 one_pos).2.2.2.2.2.2.2.2 hn1).1
  have hτhalf : least B.I x < 1 / 2 := lt_trans hτ htau2
  have hτ1 : tau1 B.I x = least B.I x := min_eq_right hτhalf.le
  obtain ⟨W, hW, hcov⟩ := GlobalTheory.DeepCover.unipotent_orbit_cover B.I x B.g q hg hn1
    (fun v => (hrk v).le) hτhalf
  have hτX : least B.I x ≤ ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b)⁻¹ ^ (11 * q) := hτ.le
  have hex := GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn8 hf hq hq2 hrd hb2
    (by exact_mod_cast hg) hτpos hτX
  have hrho : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) ≤ Real.log 2 := hex.1
  have hρ0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh
    have hg0 : (1 : ℝ) ≤ B.g := by exact_mod_cast hg
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (Real.sqrt_nonneg _)) (by linarith)) (by linarith)) (Real.rpow_nonneg (by linarith) _))
      (by norm_num)
  have hS : ∀ P, StepBoundAt B b P := GlobalTheory.T.discreteSeries_stepBound_of_countingHypotheses B Cg n₀ d p q b hn₀ hCH
  have hβ : beP B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + B.I.n ^ 2 * B.I.f) =
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := rfl
  have hβ0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := by
    rw [← hβ]; exact beP_nonneg _ _ _
  have hβle : beP B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) ≤
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := by
    rw [← hβ]; exact monotone₂ _ _ (Nat.le_add_right _ _)
  have hc0 : 0 < ∏ v, c v := Finset.prod_pos fun v _ => GlobalTheory.SobolevBound.gauge_pos (hc v)
  have hN : B.I.n ^ 2 * B.I.f = GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B := rfl
  have hK0 : 0 ≤ (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
      (Real.exp_pos _).le) (pow_nonneg (by positivity) _)) (Nat.cast_nonneg _)) hc0.le)
      ENNReal.toReal_nonneg
  have h0 : ∀ y ∈ omega B.I x W (GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x)),
      ∀ u ∈ VP B (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B), ‖vv B Fr u y‖ ≤
        Real.sqrt ((6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal) * ‖u‖ := by
    intro y hy u hu
    have hs := GlobalTheory.SobolevBound.sobolev_bound B b c (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) D T Fr hn8 hg hb19 hc hS
      hR hiso y u hu
    rw [hβ, hN] at hs
    have ht : least B.I x / 2 ≤ tau1 B.I y := by
      rw [← hτ1]; exact GlobalTheory.OmegaLeast.half_truncatedLeastLatticeSize_le_unipotentNeighbourhood B.I x W _ hn1 hrho y hy
    have hm := mult_le (n := (B.I.n : ℝ)) (by exact_mod_cast hn1) hτpos hτhalf ht
    have hle : ‖vv B Fr u y‖ ^ 2 ≤ ((6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal) * ‖u‖ ^ 2 := by
      refine hs.trans ?_
      gcongr
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hK0, Real.sqrt_sq (norm_nonneg _)] at this
  have key := GlobalTheory.DeepFamilyGap.iterate B b (GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x)) _ _
    (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) D T Fr x W hg hW hcov hS hR hcusp hρ0 (Real.sqrt_nonneg _) hβle h0
    (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) 0 (by simp) x (self_mem_omega B.I x W hρ0) (B.tens B.w)
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hDS 0).1
  rw [(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hDS 0).2, mul_one] at key
  have hA0 : 0 ≤ 2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f *
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ0) (Real.sqrt_nonneg _)) hβ0
  have hsq := pow_le_pow_left₀ (norm_nonneg _) key 2
  rw [mul_pow, ← pow_mul, Real.sq_sqrt hK0] at hsq
  refine hsq.trans (le_of_eq ?_)
  rw [show 8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * 2 = 16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B by ring]
  ring

end GlobalTheory.DeepFamilyGap
