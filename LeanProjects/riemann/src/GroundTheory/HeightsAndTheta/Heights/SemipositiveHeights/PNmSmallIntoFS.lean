import Mathlib
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.StNmSmallIntoFS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricMaxComparison
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel MvPolynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded

noncomputable section

set_option linter.unusedSectionVars false

namespace NmSmallIntoFSProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem one_mem_chartLat (y : (Σ k, ι k) → Ω) : (1 : Ω) ∈ chartLat y (fun _ => 1) 0 := by
  intro c _
  simp only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, Finset.prod_const_one, one_mul]
  exact one_mem _

theorem form_mul_mem_chartLat (y : (Σ k, ι k) → Ω) {n d : ℕ} {s : Ω} (hs : s ∈ chartLat y (fun _ => 1) n)
    {g : MRing ι} (hg : IsMultiHomog g (fun _ => d)) : aeval y g * s ∈ chartLat y (fun _ => 1) (n + d) := by
  intro c hc
  have h1 : s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * 1)) ∈ chartRingZ y c := hs c hc
  have h2 := Conductor.form_mul_invMon_mem y c hg
  rw [← Conductor.prod_zpow_eq_invMon] at h2
  have hk : ∀ k, y ⟨k, c k⟩ ^ (-(((n + d : ℕ) : ℤ) * 1)) =
      y ⟨k, c k⟩ ^ (-((n : ℤ) * 1)) * y ⟨k, c k⟩ ^ (-((d : ℕ) : ℤ)) := fun k => by
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  show aeval y g * s * ∏ k, y ⟨k, c k⟩ ^ (-(((n + d : ℕ) : ℤ) * 1)) ∈ chartRingZ y c
  rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib]
  have e : aeval y g * s * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * 1))) * ∏ k, y ⟨k, c k⟩ ^ (-((d : ℕ) : ℤ))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * 1))) * (aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((d : ℕ) : ℤ))) := by ring
  rw [e]
  exact mul_mem h1 h2

theorem secM_le_chartLat (y : (Σ k, ι k) → Ω) (n : ℕ) : secM y (fun _ => n) ≤ chartLat y (fun _ => 1) n := by
  intro x hx
  replace hx : x ∈ Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g (fun _ => n) ∧ aeval y g = s} := hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    simpa using form_mul_mem_chartLat y (one_mem_chartLat y) hg
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul r a _ ha => exact zsmul_mem ha r

theorem monomial_mul_mem_chartLatNm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (M : ℕ) (e : K → ℕ)
    (he : ∀ k, (e k : ℤ) = M - a k) (i₀ : ∀ k, ι k) (τ : ℕ) {s : Ω} (hs : s ∈ chartLatNm y a τ) :
    aeval y (chartMon i₀ e) ^ τ * s ∈ chartLatNm y (fun _ => (M : ℤ)) τ := by
  intro c hc
  have h1 := hs c hc
  have h2 : aeval y (chartMon i₀ e) * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) ∈ chartRingZ y c := by
    rw [Conductor.prod_zpow_eq_invMon]
    exact Conductor.form_mul_invMon_mem y c (homog_chartMon i₀ e)
  have h3 : aeval y (chartMon i₀ e) * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ)) ∈ integralClosure (chartRingZ y c) Ω :=
    (integralClosure (chartRingZ y c) Ω).algebraMap_mem ⟨_, h2⟩
  have hk : ∀ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * M)) =
      y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) * (y ⟨k, c k⟩ ^ (-(e k : ℤ))) ^ τ := fun k => by
    rw [← zpow_natCast (y ⟨k, c k⟩ ^ (-(e k : ℤ))), ← zpow_mul, ← zpow_add₀ (hc k)]
    congr 1
    linear_combination (τ : ℤ) * he k
  show aeval y (chartMon i₀ e) ^ τ * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * M)) ∈ _
  rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow]
  have e' : aeval y (chartMon i₀ e) ^ τ * s *
      ((∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) * (∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ))) ^ τ) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) *
        (aeval y (chartMon i₀ e) * ∏ k, y ⟨k, c k⟩ ^ (-(e k : ℤ))) ^ τ := by ring
  rw [e']
  exact mul_mem h1 (pow_mem h3 τ)

theorem exists_max_coord (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∃ c : ∀ k, ι k, ∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖ := by
  have : ∀ k, ∃ j, ∀ i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, j⟩‖ := fun k => by
    obtain ⟨i, -⟩ := hz k
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z ⟨k, i⟩‖) ⟨i, Finset.mem_univ _⟩
    exact ⟨j, fun i => hj i (Finset.mem_univ _)⟩
  choose c hc using this
  exact ⟨c, hc⟩

theorem fsH_h_eq (z : (Σ k, ι k) → ℂ) : (fsH ι).h z = ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ := by
  simp [fsH, HermLine.ofMetrics, fsMetric]

theorem coord_le_fs (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    ‖z ⟨k, i⟩‖ ≤ ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ :=
  PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) i

theorem prod_le_fsH_pow (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : ℕ) :
    ∏ k, ‖z ⟨k, c k⟩‖ ^ d ≤ (fsH ι).h z ^ d := by
  rw [fsH_h_eq, ← Finset.prod_pow]
  exact Finset.prod_le_prod (fun k _ => pow_nonneg (norm_nonneg _) _) fun k _ =>
    pow_le_pow_left₀ (norm_nonneg _) (coord_le_fs z k (c k)) d

theorem norm_eval_le_fs {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {G : MRing ι} {d : ℕ}
    (hG : IsMultiHomog G (fun _ => d)) :
    ‖eval z (map (Int.castRingHom ℂ) G)‖ ≤ coeffNorm G * (fsH ι).h z ^ d := by
  obtain ⟨c, hc⟩ := exists_max_coord z hz
  exact (norm_eval_le hc hG).trans (mul_le_mul_of_nonneg_left (prod_le_fsH_pow z c d) (coeffNorm_nonneg G))

theorem mon_mul_h_le (A : HermLine ι) {CA : ℝ} (hCA0 : 0 ≤ CA)
    (hCA : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      A.h z ≤ CA * (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) A.a).h z)
    (M : ℕ) (e : K → ℕ) (he : ∀ k, (e k : ℤ) = M - A.a k) (i₀ : ∀ k, ι k) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ * A.h z ≤ CA * (fsH ι).h z ^ M := by
  obtain ⟨c, hc⟩ := exists_max_coord z hz
  have hν : ∀ k, 0 < ‖z ⟨k, c k⟩‖ := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (norm_pos_iff.2 hi) (hc k i)
  have hsup : ∀ k, (maxMetric ℂ (ι k)).ρ (fun i => z ⟨k, i⟩) = ‖z ⟨k, c k⟩‖ := fun k =>
    le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hc k i)
      (norm_le_pi_norm (fun i => z ⟨k, i⟩) (c k))
  have hA : A.h z ≤ CA * ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k := by
    have := hCA z hz
    simp only [HermLine.ofMetrics, hsup] at this
    exact this
  have hm : ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ ≤ ∏ k, ‖z ⟨k, c k⟩‖ ^ e k := by
    rw [eval_chartMon, norm_prod]
    exact Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hc k _) _
  have hprod : (∏ k, ‖z ⟨k, c k⟩‖ ^ e k) * ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k = ∏ k, ‖z ⟨k, c k⟩‖ ^ M := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hν k).ne']
    congr 1
    rw [he k]
    ring
  calc ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ * A.h z
      ≤ (∏ k, ‖z ⟨k, c k⟩‖ ^ e k) * (CA * ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) :=
        mul_le_mul hm hA (A.pos z hz).le (Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)
    _ = CA * ∏ k, ‖z ⟨k, c k⟩‖ ^ M := by rw [← hprod]; ring
    _ ≤ CA * (fsH ι).h z ^ M := mul_le_mul_of_nonneg_left (prod_le_fsH_pow z c M) hCA0

end NmSmallIntoFSProof

open NmSmallIntoFSProof in

theorem NmSmallIntoFS.proof : NmSmallIntoFS.Statement := by
  classical
  intro K _ ι _ Ω _ y D A hV hbir hA
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    simp [mConeMap, h0]
  choose i₀ hi₀ using hy
  obtain ⟨M, hM1, haM⟩ : ∃ M : ℕ, 1 ≤ M ∧ ∀ k, A.a k ≤ M := by
    refine ⟨1 + ∑ k, (A.a k).toNat, by omega, fun k => ?_⟩
    have h1 : (A.a k).toNat ≤ ∑ k, (A.a k).toNat :=
      Finset.single_le_sum (f := fun k => (A.a k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h2 := Int.self_le_toNat (A.a k)
    omega
  let e : K → ℕ := fun k => (M - A.a k).toNat
  have he : ∀ k, (e k : ℤ) = M - A.a k := fun k => Int.toNat_of_nonneg (by linarith [haM k])
  obtain ⟨k₀, c, hc, hc0, hcond⟩ := Conductor.proof SecEq.proof K ι Ω y (fun _ => M) (fun _ => hM1)
    (fun k => ⟨i₀ k, hi₀ k⟩) hbir
  obtain ⟨CA, hCA1, hCA⟩ := MetricMaxComparison.proof K ι A hA
  let c' := c * chartMon i₀ (fun _ => M)
  have hc' : IsMultiHomog c' (fun _ => (k₀ + 1) * M) :=
    homog_congr (homog_mul hc (homog_chartMon i₀ _)) fun κ => by simp only [Pi.add_apply]; ring
  have hmon0 : ∀ d : K → ℕ, aeval y (chartMon i₀ d) ≠ 0 := fun d => by
    rw [aeval_chartMon]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hi₀ k)
  refine ⟨M, k₀ + 1, max 1 (max CA (coeffNorm c')), hM1, le_max_left _ _, fun C hC τ => ?_⟩
  have hC1 : 1 ≤ C := (le_max_left _ _).trans hC
  have hCA' : CA ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have hcn : coeffNorm c' ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans hC
  let u := aeval y c' * aeval y (chartMon i₀ e) ^ τ
  have hu : u ≠ 0 := mul_ne_zero (by simp only [c', map_mul]; exact mul_ne_zero hc0 (hmon0 _))
    (pow_ne_zero _ (hmon0 e))
  have hmem : ∀ s ∈ chartLatNm y A.a τ, u * s ∈ chartLat y (fsScaled ι C).a (M * (τ + (k₀ + 1))) := by
    intro s hs
    rw [fsScaled_a]
    have h1 := hcond τ _ (monomial_mul_mem_chartLatNm y A.a M e he i₀ τ hs)
    have h3 := form_mul_mem_chartLat y (secM_le_chartLat y ((τ + k₀) * M) h1) (homog_chartMon i₀ (fun _ => M))
    have e1 : u * s = aeval y (chartMon i₀ fun _ => M) * (aeval y c * (aeval y (chartMon i₀ e) ^ τ * s)) := by
      simp only [u, c', map_mul]
      ring
    have e2 : M * (τ + (k₀ + 1)) = (τ + k₀) * M + M := by ring
    rw [e1, e2]
    exact h3
  have hsmall : ∀ s, IsSmallH (mCoordIdeal y) y A τ s →
      IsSmallH (mCoordIdeal y) y (fsScaled ι C) (M * (τ + (k₀ + 1))) (u * s) := by
    intro s hs dg dh g h z hg hh hdeg hrep hz
    have key := hs dg (fun κ => (k₀ + 1) * M + τ * e κ + dh κ) g (c' * chartMon i₀ e ^ τ * h) z hg
      (homog_congr (homog_mul (homog_mul hc' (homog_pow (homog_chartMon i₀ e) τ)) hh)
        fun κ => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul])
      (fun κ => by
        have h1 := hdeg κ
        simp only [fsScaled_a] at h1
        push_cast at h1 ⊢
        linear_combination h1 - (τ : ℤ) * he κ)
      (by rw [hrep]; simp only [u, map_mul, map_pow]; ring) hz
    simp only [map_mul, map_pow, norm_mul, norm_pow] at key
    rw [fsScaled_h ι (by linarith) z]
    have hF : 0 ≤ (fsH ι).h z := ((fsH ι).pos z hz.1).le
    have hCF : 0 ≤ C * (fsH ι).h z := mul_nonneg (by linarith) hF
    have b1 : ‖eval z (map (Int.castRingHom ℂ) c')‖ ≤ (C * (fsH ι).h z) ^ ((k₀ + 1) * M) := by
      refine (norm_eval_le_fs hz.1 hc').trans ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (hcn.trans (le_self_pow₀ hC1 (by positivity))) (pow_nonneg hF _)
    have b2 : ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ * A.h z ≤ (C * (fsH ι).h z) ^ M := by
      refine (mon_mul_h_le A (by linarith) hCA M e he i₀ hz.1).trans ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (hCA'.trans (le_self_pow₀ hC1 (by omega))) (pow_nonneg hF _)
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖
        ≤ ‖eval z (map (Int.castRingHom ℂ) c')‖ * ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ ^ τ *
            ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := key
      _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (‖eval z (map (Int.castRingHom ℂ) c')‖ *
            (‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ * A.h z) ^ τ) := by ring
      _ ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * ((C * (fsH ι).h z) ^ ((k₀ + 1) * M) *
            ((C * (fsH ι).h z) ^ M) ^ τ) := by
        have h0 : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) (chartMon i₀ e))‖ * A.h z :=
          mul_nonneg (norm_nonneg _) (A.pos z hz.1).le
        exact mul_le_mul_of_nonneg_left (mul_le_mul b1 (pow_le_pow_left₀ h0 b2 τ) (pow_nonneg h0 _)
          (pow_nonneg hCF _)) (norm_nonneg _)
      _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (C * (fsH ι).h z) ^ (M * (τ + (k₀ + 1))) := by ring
  refine ⟨fun s => ⟨⟨u * s, hmem s s.1.2⟩, hsmall s s.2⟩, fun s t hst => ?_⟩
  have h1 : u * (s : Ω) = u * (t : Ω) := congrArg (fun x => ((x.1 : chartLat _ _ _) : Ω)) hst
  exact Subtype.ext (Subtype.ext (mul_left_cancel₀ hu h1))

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
