import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivTwoSmul

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff ZeroAtInfty InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveLoc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  have hx' : x.det ≠ 0 := hx
  have hy' : y.det ≠ 0 := hy
  show (x * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx' hy'

theorem inv_mem {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n :=
  (Matrix.isUnit_nonsing_inv_det x (isUnit_iff_ne_zero.mpr hx)).ne_zero

theorem val_mem (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero

def step (r s : ℝ) : ℝ := Real.smoothTransition (r + 1 - s)

theorem step_contDiff (r : ℝ) : ContDiff ℝ ∞ (step r) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem step_eq_one {r s : ℝ} (h : s ≤ r) : step r s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem step_eq_zero {r s : ℝ} (h : r + 1 ≤ s) : step r s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

def cutAt (r : ℝ) (x y : Mat n) : ℝ := step r (lg (x⁻¹ * y))

theorem cutAt_smooth (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) :
    ContDiffOn ℝ ∞ (cutAt r x) (GLs n) := by
  have hm : ContDiff ℝ ∞ (fun y : Mat n => x⁻¹ * y) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x⁻¹)).contDiff
  have h1 : ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) :=
    (hL n).2.2.2.1.comp hm.contDiffOn fun _ hy => mul_mem (inv_mem hx) hy
  exact (step_contDiff r).comp_contDiffOn h1

theorem cutAt_mul_unitary (hL : LgFacts) (r : ℝ) {x g : Mat n} (hx : x ∈ GLs n) (hg : g ∈ GLs n)
    (k : Matrix.unitaryGroup (Fin n) ℂ) : cutAt r x (g * k.1) = cutAt r x g := by
  have h := (hL n).2.2.1 (x⁻¹ * g) (mul_mem (inv_mem hx) hg) 1 k
  have e : ((1 : Matrix.unitaryGroup (Fin n) ℂ)).1 * (x⁻¹ * g) * k.1 = x⁻¹ * (g * k.1) := by
    rw [show ((1 : Matrix.unitaryGroup (Fin n) ℂ)).1 = 1 from rfl, one_mul, mul_assoc]
  rw [e] at h
  simp only [cutAt, h]

def cutSec {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (r : ℝ) (x : Mat n) (f : Mat n → V) : Mat n → V :=
  fun y => ((cutAt r x y : ℝ) : ℂ) • f y

theorem cutSec_mem (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) {E : KMod n} {f : Mat n → E.V}
    (hf : f ∈ CE E) : cutSec r x f ∈ CE E := by
  refine ⟨?_, fun g hg k => ?_⟩
  · have hc : ContDiffOn ℝ ∞ (fun y => ((cutAt r x y : ℝ) : ℂ)) (GLs n) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (cutAt_smooth hL r hx)
    exact hc.smul hf.1
  · simp only [cutSec, cutAt_mul_unitary hL r hx hg k, hf.2 g hg k, map_smul]

theorem cutSec_cpt (hL : LgFacts) (r : ℝ) {x : Mat n} (hx : x ∈ GLs n) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (f : Mat n → V) : Cpt (cutSec r x f) := by
  refine ⟨lg x + (r + 1), fun y hy h => ?_⟩
  have e : x * (x⁻¹ * y) = y := Matrix.mul_nonsing_inv_cancel_left x y (isUnit_iff_ne_zero.mpr hx)
  have hs := (hL n).1 x hx (x⁻¹ * y) (mul_mem (inv_mem hx) hy)
  rw [e] at hs
  have h0 : cutAt r x y = 0 := step_eq_zero (by linarith)
  simp [cutSec, h0]

theorem cutSec_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℝ} {x y : Mat n} (hx : x ∈ GLs n)
    (f : Mat n → V) (h : lg y ≤ r) : cutSec r x f (x * y) = f (x * y) := by
  have e : x⁻¹ * (x * y) = y := Matrix.nonsing_inv_mul_cancel_left x y (isUnit_iff_ne_zero.mpr hx)
  have h1 : cutAt r x (x * y) = 1 := by
    rw [cutAt, e]
    exact step_eq_one h
  simp [cutSec, h1]

theorem wave_sub {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E fun t y => u t y - v t y := by
  have h := GlobalTheory.CompanionTheory.WaveK.Lin.wave_add hu (GlobalTheory.CompanionTheory.WaveK.Lin.wave_smul (-1 : ℂ) hv)
  simpa [sub_eq_add_neg] using h

theorem kerLoc : KerLoc := by
  intro n _ _ μ _ E g T k hg hL _ _ hS hW hk hsupp heq hker
  refine ⟨hk, hsupp, heq, fun u hu x hx => ?_⟩
  obtain ⟨R, hR⟩ := hsupp
  obtain ⟨c, hc⟩ := hS n
  obtain ⟨r, hRr, hcr⟩ : ∃ r : ℝ, R ≤ r ∧ |c| * (1 + |T|) ≤ r :=
    ⟨max R (|c| * (1 + |T|)), le_max_left _ _, le_max_right _ _⟩
  have hf := cutSec_mem hL r hx (hu.2.1 0)
  have hcpt := cutSec_cpt hL r hx (u 0)
  obtain ⟨v, hv, hv0⟩ := hW n E _ hf hcpt
  have huv : ∀ t, |t| ≤ T → u t x = v t x := by
    intro t ht
    refine sub_eq_zero.mp (hc E _ (wave_sub hu hv) t x hx fun y hy hly => ?_)
    have hb : c * (1 + |t|) ≤ |c| * (1 + |T|) := by
      have h1 : |t| ≤ |T| := ht.trans (le_abs_self T)
      have h2 : (0 : ℝ) ≤ 1 + |t| := by positivity
      calc c * (1 + |t|) ≤ |c| * (1 + |t|) := mul_le_mul_of_nonneg_right (le_abs_self c) h2
        _ ≤ |c| * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
    show u 0 (x * y) - v 0 (x * y) = 0
    rw [hv0 _ (mul_mem hx hy), cutSec_eq hx _ (hly.trans (hb.trans hcr)), sub_self]
  have h1 : act μ E k (u 0) x = act μ E k (cutSec r x (u 0)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show k y.val (u 0 (x * y.val)) = k y.val (cutSec r x (u 0) (x * y.val))
    by_cases h : R < lg y.val
    · simp [hR _ (val_mem y) h]
    · rw [cutSec_eq hx _ ((not_lt.mp h).trans hRr)]
  rw [h1, hker _ hf hcpt v hv hv0 x hx]
  show _ = ∫ t, (g t : ℂ) • u t x
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show (g t : ℂ) • v t x = (g t : ℂ) • u t x
  by_cases h : T < |t|
  · simp [hg.2.2 t h]
  · rw [huv t (not_lt.mp h)]

end GlobalTheory.CompanionTheory.WaveLoc
