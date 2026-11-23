import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpowTSucc

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.Ibp

variable {n : ℕ}

section Int

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem integrable_of_cpt (hL : LgFacts) {φ : Mat n → ℂ} (hφ : ContinuousOn φ (GLs n)) (cφ : Cpt φ) :
    Integrable (fun y : G n => φ y.val) μ := by
  obtain ⟨R, hR⟩ := cφ
  have hc : Continuous (fun y : G n => φ y.val) :=
    hφ.comp_continuous Units.continuous_val val_mem
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_)
  intro y hy
  exact hR _ (val_mem y) (not_le.1 hy)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem sm_inner {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => ⟪f y, h y⟫_ℂ) (GLs n) :=
  hf.inner ℂ hh

theorem Cpt_inner {f h : Mat n → V} (cf : Cpt f) : Cpt (fun y => ⟪f y, h y⟫_ℂ) := by
  obtain ⟨R, hR⟩ := cf
  exact ⟨R, fun y hy hl => by simp [hR y hy hl]⟩

theorem Cpt_inner' {f h : Mat n → V} (ch : Cpt h) : Cpt (fun y => ⟪f y, h y⟫_ℂ) := by
  obtain ⟨R, hR⟩ := ch
  exact ⟨R, fun y hy hl => by simp [hR y hy hl]⟩

theorem int_inner (hL : LgFacts) {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) :
    Integrable (fun y : G n => ⟪f y.val, h y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (sm_inner hf hh).continuousOn (Cpt_inner cf)

theorem int_inner' (hL : LgFacts) {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (ch : Cpt h) :
    Integrable (fun y : G n => ⟪f y.val, h y.val⟫_ℂ) μ :=
  integrable_of_cpt μ hL (sm_inner hf hh).continuousOn (Cpt_inner' ch)

theorem ibp_Rd (hL : LgFacts) (hR : RCalc) (X : Mat n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Rd X f y.val, h y.val⟫_ℂ ∂μ = -∫ y : G n, ⟪f y.val, Rd X h y.val⟫_ℂ ∂μ := by
  have h0 := (hR n).2.2 μ ℂ (fun y => ⟪f y, h y⟫_ℂ) (sm_inner hf hh) (Cpt_inner cf) X
  have e : ∀ y : G n, Rd X (fun y => ⟪f y, h y⟫_ℂ) y.val =
      ⟪f y.val, Rd X h y.val⟫_ℂ + ⟪Rd X f y.val, h y.val⟫_ℂ := by
    intro y
    exact fderiv_inner_apply ℂ (diffAt hf (val_mem y)) (diffAt hh (val_mem y)) _
  simp_rw [e] at h0
  rw [integral_add (int_inner' μ hL hf (sm_Rd hR X hh) (Cpt_Rd hL X ch))
    (int_inner μ hL (sm_Rd hR X hf) hh (Cpt_Rd hL X cf))] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem ibp_Eu (hL : LgFacts) (hR : RCalc) (s : Bool) (a b : Fin n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Eu s a b f y.val, h y.val⟫_ℂ ∂μ = -∫ y : G n, ⟪f y.val, Eu (!s) a b h y.val⟫_ℂ ∂μ := by
  set X : Mat n := Matrix.single a b 1
  set Y : Mat n := Matrix.single a b Complex.I
  set c : ℂ := if !s then -Complex.I else Complex.I with hc
  have hc' : conj (if s then -Complex.I else Complex.I) = c := by
    cases s <;> simp [hc]
  have e1 : ∀ y : G n, ⟪Eu s a b f y.val, h y.val⟫_ℂ =
      (1 / 2 : ℂ) * (⟪Rd X f y.val, h y.val⟫_ℂ + c * ⟪Rd Y f y.val, h y.val⟫_ℂ) := by
    intro y
    have h2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    simp only [Eu, Pi.smul_apply, Pi.add_apply, inner_smul_left, inner_add_left, hc', h2]
    rfl
  have e2 : ∀ y : G n, ⟪f y.val, Eu (!s) a b h y.val⟫_ℂ =
      (1 / 2 : ℂ) * (⟪f y.val, Rd X h y.val⟫_ℂ + c * ⟪f y.val, Rd Y h y.val⟫_ℂ) := by
    intro y
    simp only [Eu, Pi.smul_apply, Pi.add_apply, inner_smul_right, inner_add_right]
    simp [X, Y, hc]
  simp_rw [e1, e2]
  rw [integral_const_mul, integral_const_mul,
    integral_add (int_inner μ hL (sm_Rd hR X hf) hh (Cpt_Rd hL X cf))
      ((int_inner μ hL (sm_Rd hR Y hf) hh (Cpt_Rd hL Y cf)).const_mul c),
    integral_add (int_inner' μ hL hf (sm_Rd hR X hh) (Cpt_Rd hL X ch))
      ((int_inner' μ hL hf (sm_Rd hR Y hh) (Cpt_Rd hL Y ch)).const_mul c),
    integral_const_mul, integral_const_mul, ibp_Rd μ hL hR X hf hh cf ch, ibp_Rd μ hL hR Y hf hh cf ch]
  ring

theorem ibp_Epow (hL : LgFacts) (hR : RCalc) (s : Bool) (m : ℕ) (a b : Fin n) {f h : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Epow s m a b f y.val, h y.val⟫_ℂ ∂μ =
      (-1 : ℂ) ^ m * ∫ y : G n, ⟪f y.val, EpowT (!s) m b a h y.val⟫_ℂ ∂μ := by
  induction m generalizing a h with
  | zero =>
    by_cases hab : a = b
    · subst hab
      simp [Epow, EpowT]
    · simp [Epow, EpowT, hab, Ne.symm hab]
  | succ m ih =>
    have e1 : ∀ y : G n, ⟪Epow s (m + 1) a b f y.val, h y.val⟫_ℂ =
        ∑ c, ⟪Eu s a c (Epow s m c b f) y.val, h y.val⟫_ℂ := by
      intro y
      simp only [Epow, Finset.sum_apply, sum_inner]
    have e2 : ∀ y : G n, ⟪f y.val, EpowT (!s) (m + 1) b a h y.val⟫_ℂ =
        ∑ c, ⟪f y.val, EpowT (!s) m b c (Eu (!s) a c h) y.val⟫_ℂ := by
      intro y
      rw [EpowT_succ' hR (!s) m a b hh (val_mem y), Finset.sum_apply, inner_sum]
    simp_rw [e1, e2]
    rw [integral_finset_sum _ fun c _ => int_inner μ hL (sm_Eu hR s a c (sm_Epow hR s m c b hf)) hh
        (Cpt_Eu hL s a c (Cpt_Epow hL s m c b cf)),
      integral_finset_sum _ fun c _ => int_inner μ hL hf
        (sm_EpowT hR (!s) m b c (sm_Eu hR (!s) a c hh)) cf,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ibp_Eu μ hL hR s a c (sm_Epow hR s m c b hf) hh (Cpt_Epow hL s m c b cf) ch,
      ih c (sm_Eu hR (!s) a c hh) (Cpt_Eu hL (!s) a c ch), pow_succ]
    ring

end Int

theorem ibp_gel : LgFacts → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)]
    (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (s : Bool) (m : ℕ) (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
    ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h →
    ∫ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ ∂μ =
      (-1 : ℂ) ^ m * ∫ y : G n, ⟪f y.val, gelT (!s) m h y.val⟫_ℂ ∂μ := by
  intro hL hR n _ _ μ _ V _ _ _ s m f h hf hh cf ch
  have e1 : ∀ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ = ∑ a, ⟪Epow s m a a f y.val, h y.val⟫_ℂ := by
    intro y
    simp only [gel, Finset.sum_apply, sum_inner]
  have e2 : ∀ y : G n, ⟪f y.val, gelT (!s) m h y.val⟫_ℂ =
      ∑ a, ⟪f y.val, EpowT (!s) m a a h y.val⟫_ℂ := by
    intro y
    simp only [gelT, Finset.sum_apply, inner_sum]
  simp_rw [e1, e2]
  rw [integral_finset_sum _ fun a _ => int_inner μ hL (sm_Epow hR s m a a hf) hh
      (Cpt_Epow hL s m a a cf),
    integral_finset_sum _ fun a _ => int_inner μ hL hf (sm_EpowT hR (!s) m a a hh) cf,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => ibp_Epow μ hL hR s m a a hf hh cf ch

end GlobalTheory.CompanionTheory.WaveMult.Ibp
