import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev cj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun q => starRingEnd ℂ (z q)

theorem cj_cj (z : (Σ k, ι k) → ℂ) : cj (cj z) = z := by
  funext q; simp [cj]

theorem cj_nonzero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, cj z ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, by simpa [cj] using hi⟩

theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp [mul_assoc]

theorem sameOrbit_refl (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

theorem sameOrbit_cj {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit (cj z) (cj z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => starRingEnd ℂ (c k), fun k => by simpa using hc k, ?_⟩
  funext p
  simp [cj]

theorem cj_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : cj z ∈ mcPts P := by
  refine ⟨cj_nonzero hz.1, fun f hf => ?_⟩
  have h := hz.2 f hf
  have key : eval (cj z) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
    rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq,
      map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [map_mul, map_prod, map_pow]
  rw [key, h, map_zero]

theorem log_sub_orbit (A B : HermLine ι) (hab : A.a = B.a) {z z' : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : SameOrbit z z') :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h z') - Real.log (B.h z') := by
  obtain ⟨c, hc, rfl⟩ := h
  have hP : 0 < ∏ k, ‖c k‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  rw [A.smul c z' hc, B.smul c z' hc, ← hab,
    Real.log_mul hP.ne' (A.pos z' hz).ne', Real.log_mul hP.ne' (B.pos z' hz).ne']
  ring

def conjAvg (A : HermLine ι) : HermLine ι where
  a := A.a
  h z := Real.sqrt |A.h z * A.h (cj z)|
  pos z hz := Real.sqrt_pos.2 (abs_pos.2 (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz))).ne')
  smul c z hc := by
    have hP : 0 ≤ ∏ k, ‖c k‖ ^ A.a k :=
      Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
    have e1 : cj (fun p : Σ k, ι k => c p.1 * z p) =
        fun p => (starRingEnd ℂ (c p.1)) * cj z p := by
      funext p; simp [cj]
    have hc' : ∀ k, starRingEnd ℂ (c k) ≠ 0 := fun k => by simpa using hc k
    rw [e1, A.smul c z hc, A.smul _ (cj z) hc']
    simp only [RCLike.norm_conj]
    rw [show (∏ k, ‖c k‖ ^ A.a k) * A.h z * ((∏ k, ‖c k‖ ^ A.a k) * A.h (cj z)) =
      (∏ k, ‖c k‖ ^ A.a k) ^ 2 * (A.h z * A.h (cj z)) by ring, abs_mul, abs_of_nonneg (sq_nonneg _),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hP]

theorem conjAvg_conj (A : HermLine ι) : IsConjInvariantH (conjAvg A) := fun z => by
  change Real.sqrt |A.h (cj z) * A.h (cj (cj z))| = Real.sqrt |A.h z * A.h (cj z)|
  rw [cj_cj, mul_comm]

theorem conjAvg_log (A : HermLine ι) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((conjAvg A).h z) = (Real.log (A.h z) + Real.log (A.h (cj z))) / 2 := by
  have h1 := A.pos z hz
  have h2 := A.pos _ (cj_nonzero hz)
  change Real.log (Real.sqrt |A.h z * A.h (cj z)|) = _
  rw [abs_of_pos (mul_pos h1 h2), Real.log_sqrt (mul_pos h1 h2).le, Real.log_mul h1.ne' h2.ne']

theorem conjAvg_smooth {A : HermLine ι} (hA : IsSmoothHerm A) : IsSmoothHerm (conjAvg A) := by
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hS
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cj : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) := by
    refine contDiff_pi.2 fun q => ?_
    exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ q)
  have hmap : Set.MapsTo (cj : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) S S := fun z hz => cj_nonzero hz
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h (cj z)) S :=
    hA.comp hconj.contDiffOn hmap
  have hprod := hA.mul h2
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.sqrt (A.h z * A.h (cj z))) S :=
    hprod.sqrt fun z hz => (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz))).ne'
  refine hs.congr fun z hz => ?_
  change Real.sqrt |A.h z * A.h (cj z)| = _
  rw [abs_of_pos (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz)))]

theorem holoOn_comp {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {g : X → Y} (hg : HoloMap A B g) {V : Set Y}
    {G : Y → ℂ} (hG : B.HoloOn V G) : A.HoloOn (g ⁻¹' V) (G ∘ g) := by
  intro j w hw
  obtain ⟨k, hk⟩ := B.cover (g ((A.chart j).symm w))
  have hw' : w ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (g ⁻¹' (B.chart k).source) := ⟨hw.1, hk⟩
  have h1 := hg.2 j k w hw'
  have h2 : AnalyticAt ℂ (G ∘ (B.chart k).symm) ((B.chart k ∘ g ∘ (A.chart j).symm) w) := by
    refine hG k _ ⟨(B.chart k).map_source hk, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (B.chart k).left_inv hk]
    exact hw.2
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hc : ContinuousAt (g ∘ (A.chart j).symm) w :=
    hg.1.continuousAt.comp ((A.chart j).continuousAt_symm hw.1)
  filter_upwards [hc ((B.chart k).open_source.mem_nhds hk)] with w' hw''
  have hw3 : g ((A.chart j).symm w') ∈ (B.chart k).source := hw''
  simp only [Function.comp, (B.chart k).left_inv hw3]

def IsLiftSys {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : Ideal (MRing ι))
    (U : X → Set X) (lift : X → X → (Σ k, ι k) → ℂ) : Prop :=
  (∀ x, IsOpen (U x)) ∧ (∀ x, x ∈ U x) ∧ (∀ x p, A.HoloOn (U x) fun y => lift x y p) ∧
  (∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P) ∧
  (∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)) ∧
  (∀ z ∈ mcPts P, ∃ x, SameOrbit (lift x x) z) ∧
  (∀ x x', SameOrbit (lift x x) (lift x' x') → x = x') ∧
  ∀ x, ∀ p : (k : K) → ι k, (∀ k, lift x x ⟨k, p k⟩ ≠ 0) → ∀ j, x ∈ (A.chart j).source →
    (fderiv ℂ (fun y => affCoord p (lift x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

end GlobalTheory.CompanionTheory.Ar.PB.Cj
