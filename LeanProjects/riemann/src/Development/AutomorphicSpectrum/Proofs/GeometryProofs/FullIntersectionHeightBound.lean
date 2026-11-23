import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StrictWeightGrowthBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithmeticDegreePositiveHermStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightThresholdLimitCoefficientsStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricMaxComparison
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug.Count

open MvPolynomial GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem cauchy_bound {D : ℕ} (L : ℕ → ℝ) (hL : ∀ j, 0 ≤ L j) {a b : ℝ} (hb : 0 ≤ b)
    (h : a ^ D ≤ ∑ j ∈ Finset.range D, L j * a ^ j * b ^ (D - j)) :
    a ≤ (1 + ∑ j ∈ Finset.range D, L j) * b := by
  by_contra hlt
  rw [not_le] at hlt
  set S := ∑ j ∈ Finset.range D, L j with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => hL j
  have hB : 1 ≤ 1 + S := by linarith
  have hB0 : 0 < 1 + S := by linarith
  have ha0 : 0 < a := lt_of_le_of_lt (mul_nonneg hB0.le hb) hlt
  have hba : b ≤ a / (1 + S) := by rw [le_div_iff₀ hB0]; linarith
  have hterm : ∀ j ∈ Finset.range D, L j * a ^ j * b ^ (D - j) ≤ L j * (a ^ D / (1 + S)) := by
    intro j hj
    have hj' : j < D := Finset.mem_range.mp hj
    obtain ⟨m, hm⟩ : ∃ m, D - j = m + 1 := ⟨D - j - 1, by omega⟩
    have h1 : b ^ (D - j) ≤ a ^ (D - j) / (1 + S) := by
      rw [hm]
      calc b ^ (m + 1) ≤ (a / (1 + S)) ^ (m + 1) := pow_le_pow_left₀ hb hba _
        _ = a ^ (m + 1) / (1 + S) ^ (m + 1) := div_pow _ _ _
        _ ≤ a ^ (m + 1) / (1 + S) := by
            apply div_le_div_of_nonneg_left (by positivity) hB0
            calc 1 + S = (1 + S) ^ 1 := (pow_one _).symm
              _ ≤ (1 + S) ^ (m + 1) := pow_le_pow_right₀ hB (by omega)
    have h2 : a ^ j * a ^ (D - j) = a ^ D := by rw [← pow_add]; congr 1; omega
    calc L j * a ^ j * b ^ (D - j) ≤ L j * a ^ j * (a ^ (D - j) / (1 + S)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (hL j) (by positivity))
      _ = L j * (a ^ j * a ^ (D - j) / (1 + S)) := by ring
      _ = _ := by rw [h2]
  have hsum : a ^ D ≤ S * (a ^ D / (1 + S)) := by
    refine h.trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [hS, Finset.sum_mul]
  have hpos : 0 < a ^ D := by positivity
  have : S * (a ^ D / (1 + S)) < a ^ D := by
    rw [mul_div_assoc', div_lt_iff₀ hB0]
    nlinarith
  linarith

theorem exists_integral_bound (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (d : K → ℕ) (G F : MRing ι) (z : (Σ k, ι k) → ℂ),
      IsMultiHomog G d → IsMultiHomog F d → aeval y G = x * aeval y F → z ∈ mcPts (mCoordIdeal y) →
      (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) → (∀ k, z ⟨k, c k⟩ ≠ 0) →
      ‖eval z (map (Int.castRingHom ℂ) G)‖ ≤ B * ‖eval z (map (Int.castRingHom ℂ) F)‖ := by
  classical
  obtain ⟨p, pm, hp⟩ := hx
  set D := p.natDegree with hD
  have hform : ∀ j : ℕ, ∃ (δ : K → ℕ) (e : MRing ι), IsMultiHomog e δ ∧
      aeval y e = ((p.coeff j : chartRingZ y c) : Ω) * ∏ k, y ⟨k, c k⟩ ^ δ k := fun j =>
    exists_form_of_mem_chartRingZ y c hc (p.coeff j).2
  choose δ e he hev using hform
  set Δ : K → ℕ := ∑ j ∈ Finset.range D, δ j with hΔ
  have hle : ∀ j ∈ Finset.range D, ∀ k, δ j k ≤ Δ k := by
    intro j hj k
    rw [hΔ, Finset.sum_apply]
    exact Finset.single_le_sum (f := fun j => δ j k) (fun _ _ => Nat.zero_le _) hj
  let Fm : ℕ → MRing ι := fun j => e j * chartMon c (Δ - δ j)
  have hFm : ∀ j ∈ Finset.range D, IsMultiHomog (Fm j) Δ := fun j hj =>
    homog_congr (homog_mul (he j) (homog_chartMon c (Δ - δ j))) fun k => by
      simp only [Pi.add_apply, Pi.sub_apply]
      have := hle j hj k
      omega
  have hFmv : ∀ j ∈ Finset.range D, aeval y (Fm j) =
      ((p.coeff j : chartRingZ y c) : Ω) * ∏ k, y ⟨k, c k⟩ ^ Δ k := by
    intro j hj
    simp only [Fm, map_mul, aeval_chartMon, hev]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add]
    congr 1
    simp only [Pi.sub_apply]
    have := hle j hj k
    omega
  refine ⟨1 + ∑ j ∈ Finset.range D, coeffNorm (Fm j),
    add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => coeffNorm_nonneg _), ?_⟩
  intro d G F z hG hF hGF hz hmax hz0
  have heq : x ^ D + ∑ j ∈ Finset.range D, ((p.coeff j : chartRingZ y c) : Ω) * x ^ j = 0 := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, ← hD] at hp
    have h1 : p.coeff D = 1 := pm.coeff_natDegree
    rw [h1, map_one, one_mul] at hp
    rw [add_comm]
    exact hp
  let Q : MRing ι := chartMon c Δ * G ^ D + ∑ j ∈ Finset.range D, Fm j * G ^ j * F ^ (D - j)
  have hQ : IsMultiHomog Q (Δ + D • d) := by
    refine homog_add (homog_mul (homog_chartMon c Δ) (homog_pow hG D)) (homog_sum _ fun j hj => ?_)
    refine homog_congr (homog_mul (homog_mul (hFm j hj) (homog_pow hG j)) (homog_pow hF (D - j))) fun k => ?_
    have hj' : j ≤ D := (Finset.mem_range.mp hj).le
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : j * d k + (D - j) * d k = D * d k := by rw [← add_mul]; congr 1; omega
    omega
  have hQy : aeval y Q = 0 := by
    simp only [Q, map_add, map_mul, map_pow, map_sum, aeval_chartMon, hGF]
    have : ∀ j ∈ Finset.range D, aeval y (Fm j) * (x * aeval y F) ^ j * aeval y F ^ (D - j) =
        (∏ k, y ⟨k, c k⟩ ^ Δ k) * aeval y F ^ D * (((p.coeff j : chartRingZ y c) : Ω) * x ^ j) := by
      intro j hj
      rw [hFmv j hj, mul_pow]
      have : aeval y F ^ D = aeval y F ^ j * aeval y F ^ (D - j) := by
        rw [← pow_add]; congr 1; have := Finset.mem_range.mp hj; omega
      rw [this]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, mul_pow]
    calc _ = (∏ k, y ⟨k, c k⟩ ^ Δ k) * aeval y F ^ D *
          (x ^ D + ∑ j ∈ Finset.range D, ((p.coeff j : chartRingZ y c) : Ω) * x ^ j) := by ring
      _ = 0 := by rw [heq, mul_zero]
  have hQz := vanish hz hQ hQy
  simp only [Q, map_add, map_mul, map_pow, map_sum, eval_chartMon] at hQz
  set gz := eval z (map (Int.castRingHom ℂ) G) with hgz
  set fz := eval z (map (Int.castRingHom ℂ) F) with hfz
  set Pz := ∏ k, ‖z ⟨k, c k⟩‖ ^ Δ k with hPz
  have hPpos : 0 < Pz := Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hz0 k)) _
  have hmain : Pz * ‖gz‖ ^ D ≤ Pz * ∑ j ∈ Finset.range D, coeffNorm (Fm j) * ‖gz‖ ^ j * ‖fz‖ ^ (D - j) := by
    have e1 : (∏ k, z ⟨k, c k⟩ ^ Δ k) * gz ^ D =
        -∑ j ∈ Finset.range D, eval z (map (Int.castRingHom ℂ) (Fm j)) * gz ^ j * fz ^ (D - j) :=
      eq_neg_of_add_eq_zero_left hQz
    have e2 : Pz * ‖gz‖ ^ D = ‖(∏ k, z ⟨k, c k⟩ ^ Δ k) * gz ^ D‖ := by
      rw [norm_mul, norm_prod, norm_pow]
      simp only [norm_pow, hPz]
    rw [e2, e1, norm_neg, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    have := norm_eval_le hmax (hFm j hj)
    calc _ ≤ (coeffNorm (Fm j) * Pz) * ‖gz‖ ^ j * ‖fz‖ ^ (D - j) := by gcongr
      _ = _ := by ring
  have h2 := le_of_mul_le_mul_left hmain hPpos
  exact cauchy_bound (fun j => coeffNorm (Fm j)) (fun _ => coeffNorm_nonneg _) (norm_nonneg _) h2

theorem exists_upper_nm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLatNm y a n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
      IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + n * a k) →
      aeval y g = s * aeval y h → z ∈ mcPts (mCoordIdeal y) →
      (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) → (∀ k, z ⟨k, c k⟩ ≠ 0) →
      ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
        B * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * a k) := by
  obtain ⟨B, hB0, hB⟩ := exists_integral_bound y c hc (hs c hc)
  refine ⟨B, hB0, ?_⟩
  intro dg dh g h z hg hh hd hgy hz hmax hz0
  let up : K → ℕ := fun k => ((n : ℤ) * a k).toNat
  let dn : K → ℕ := fun k => (-((n : ℤ) * a k)).toNat
  have hud : ∀ k, (up k : ℤ) - dn k = (n : ℤ) * a k := fun k => by
    simp only [up, dn]; omega
  have hdeg : ∀ k, (dg + dn) k = (dh + up) k := fun k => by
    have h1 := hd k
    have h2 := hud k
    simp only [Pi.add_apply]
    omega
  have hG : IsMultiHomog (g * chartMon c dn) (dh + up) :=
    homog_congr (homog_mul hg (homog_chartMon c dn)) hdeg
  have hF : IsMultiHomog (h * chartMon c up) (dh + up) := homog_mul hh (homog_chartMon c up)
  have hval : aeval y (g * chartMon c dn) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * aeval y (h * chartMon c up) := by
    simp only [map_mul, aeval_chartMon, hgy]
    have : (∏ k, y ⟨k, c k⟩ ^ dn k) = (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ up k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
      congr 1
      have := hud k
      omega
    rw [this]
    ring
  have h1 := hB _ _ _ z hG hF hval hz hmax hz0
  simp only [map_mul, eval_chartMon, norm_mul, norm_prod, norm_pow] at h1
  have hr : ∀ k, ‖z ⟨k, c k⟩‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hz0 k)
  have hDn : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ dn k := Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hz0 k)) _
  have hUp : ∏ k, ‖z ⟨k, c k⟩‖ ^ up k = (∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * a k)) * ∏ k, ‖z ⟨k, c k⟩‖ ^ dn k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hr k)]
    congr 1
    have := hud k
    omega
  rw [hUp] at h1
  refine le_of_mul_le_mul_right ?_ hDn
  calc _ ≤ _ := h1
    _ = _ := by ring

noncomputable def invLine (A : HermLine ι) : HermLine ι where
  a := fun k => - A.a k
  h z := (A.h z)⁻¹
  pos z hz := inv_pos.mpr (A.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_neg]

theorem exists_lower_max (A : HermLine ι) (hA : IsSmoothHerm A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) → ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k ≤ M * A.h z := by
  have hI : IsSmoothHerm (invLine A) := by
    unfold IsSmoothHerm at hA ⊢
    exact hA.inv fun z hz => (A.pos z hz).ne'
  obtain ⟨C, hC1, hC⟩ := MetricMaxComparison.proof K ι (invLine A) hI
  refine ⟨C, by linarith, fun z c hz hmax => ?_⟩
  have h1 := hC z hz
  have hn : ∀ k, ‖fun i : ι k => z ⟨k, i⟩‖ = ‖z ⟨k, c k⟩‖ := fun k =>
    le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hmax k i)
      (norm_le_pi_norm (fun i : ι k => z ⟨k, i⟩) (c k))
  have hz0 : ∀ k, 0 < ‖z ⟨k, c k⟩‖ := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (norm_pos_iff.mpr hi) (hmax k i)
  have h2 : (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) (invLine A).a).h z =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ := by
    show ∏ k, ‖fun i : ι k => z ⟨k, i⟩‖ ^ (- A.a k) = _
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hn k, zpow_neg]
  rw [h2] at h1
  have hP : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (hz0 k) _
  have hh : 0 < A.h z := A.pos z hz
  have h3 : (A.h z)⁻¹ ≤ C * (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ := h1
  rw [inv_le_iff_one_le_mul₀ hh] at h3
  have h4 := mul_le_mul_of_nonneg_right h3 hP.le
  rw [one_mul] at h4
  calc _ ≤ _ := h4
    _ = C * A.h z * ((∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) := by ring
    _ = C * A.h z := by rw [inv_mul_cancel₀ hP.ne', mul_one]

theorem bounded_section_smooth_metric (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (s : Ω) (hA : IsSmoothHerm A)
    (hs : s ∈ chartLatNm y A.a τ) :
    ∃ C : ℝ, 0 < C ∧ IsBoundedH (mCoordIdeal y) y A τ C s := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_lower_max A hA
  choose B hB0 hB using fun c hc => exists_upper_nm y A.a τ hs c hc
  refine ⟨1 + (∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0), ?_, ?_⟩
  · refine add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun c' _ => ?_)
    split_ifs with hc'
    · exact mul_nonneg (hB0 c' hc') (pow_nonneg hM0 τ)
    · exact le_rfl
  intro dg dh g h z hg hh hdeg hgy hz
  have hmax : ∀ k, ∃ i, ∀ i', ‖z ⟨k, i'⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz.1 k
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z ⟨k, i⟩‖) ⟨i0, Finset.mem_univ _⟩
    exact ⟨i, fun i' => hi i' (Finset.mem_univ _)⟩
  choose c hcmax using hmax
  have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have := hcmax k i0
    rw [h0, norm_zero] at this
    exact hi0 (norm_le_zero_iff.mp this)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hz0 k (by
    have := vanish hz (homog_X ⟨k, c k⟩) (by rw [aeval_X]; exact h0)
    simpa using this)
  have h1 := hB c hyc dg dh g h z hg hh hdeg hgy hz hcmax hz0
  have h2 := hM z c hz.1 hcmax
  have hpow : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) ^ τ := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]
  have h3 : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) ≤ M ^ τ * A.h z ^ τ := by
    rw [hpow, ← mul_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _) h2 τ
  have hCge : B c hyc * M ^ τ ≤
      ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0 := by
    have := Finset.single_le_sum (f := fun c : (∀ k, ι k) =>
        if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0)
      (fun c' _ => by
        split_ifs with hc'
        · exact mul_nonneg (hB0 c' hc') (pow_nonneg hM0 τ)
        · exact le_rfl) (Finset.mem_univ c)
    simpa only [dif_pos hyc] using this
  have hAh : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) := h1
    _ ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * (M ^ τ * A.h z ^ τ) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (hB0 c hyc) (norm_nonneg _))
    _ = (B c hyc * M ^ τ) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by ring
    _ ≤ (1 + ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0) *
          ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
        have : B c hyc * M ^ τ ≤ 1 + ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0 := by
          linarith
        gcongr

end GlobalTheory.CompanionTheory.Ar.Plug.Count

namespace GlobalTheory.CompanionTheory.Ar.Plug.Count

theorem cmType_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    Nonempty (CMType H) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, h0]; simp
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre : (τ (H.rt : E)).re = 0 := by
    have a := congrArg Complex.re h1
    have b := congrArg Complex.im h1
    simp [sq] at a b
    by_contra hne
    have : (τ (H.rt : E)).im = 0 := by
      have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at a
    nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact ⟨⟨τ, h⟩⟩
  · refine ⟨⟨(starRingEnd ℂ).comp τ, ?_⟩⟩
    have : H.rt0 = -τ (H.rt : E) := by rw [h, neg_neg]
    rw [this]
    apply Complex.ext <;> simp [hre]

end GlobalTheory.CompanionTheory.Ar.Plug.Count

namespace GlobalTheory.CompanionTheory.Ar.Plug.Count

open MvPolynomial in

theorem charZero_of_arith {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {d : ℕ} (h : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  have hz : ∀ n : ℤ, (n : Ω) = 0 → n = 0 := by
    intro n hn
    have h1 : (C n : MRing ι) ∈ mCoordIdeal y := by
      show C n ∈ RingHom.ker (mConeMap y)
      rw [RingHom.mem_ker]
      rw [mConeMap, MvPolynomial.aeval_C, eq_intCast, ← map_intCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    have h2 : n ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := h1
    rw [h.2.2.1] at h2
    simpa using h2
  refine ⟨fun a b hab => ?_⟩
  have := hz ((a : ℤ) - b) (by push_cast; rw [hab, sub_self])
  omega

theorem small_shift {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ q : ℕ} {s : Ω} {c : ℝ} (hτ : 0 < τ) (hq : 0 < q) (hc : 0 < c)
    (h : GroundTheory.Heights₂.Heights.HilbertSamuel.IsBoundedH (mCoordIdeal y) y A τ c s) :
    ∃ t : ℝ, IsSmallH (mCoordIdeal y) y (Small.shiftH A (q * t)) τ s := by
  refine ⟨Real.log c / (τ * q), ?_⟩
  intro dg dh g h' z hg hh hdeg he hz
  have h0 := h dg dh g h' z hg hh hdeg he hz
  have hτ' : (τ : ℝ) ≠ 0 := by positivity
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have e1 : (Small.shiftH A ((q : ℝ) * (Real.log c / (τ * q)))).h z ^ τ = c * A.h z ^ τ := by
    show (Real.exp ((q : ℝ) * (Real.log c / (τ * q))) * A.h z) ^ τ = _
    rw [mul_pow, ← Real.exp_nat_mul]
    have : (τ : ℝ) * ((q : ℝ) * (Real.log c / (τ * q))) = Real.log c := by field_simp
    rw [this, Real.exp_log hc]
  rw [e1]
  calc _ ≤ _ := h0
    _ = _ := by ring

theorem indep_mul {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ} (v : Fin r → Ω) (hv : LinearIndependent ℚ v)
    {t : Ω} (ht : t ≠ 0) : LinearIndependent ℤ (fun i => v i * t) := by
  have h1 : LinearIndependent ℤ v :=
    hv.restrict_scalars (fun a b h => by simpa using h)
  exact h1.map' (LinearMap.mulRight ℤ t) (LinearMap.ker_eq_bot.mpr (mul_left_injective₀ ht))

end GlobalTheory.CompanionTheory.Ar.Plug.Count

open GlobalTheory.CompanionTheory.Ar.Plug.Count in

theorem GlobalTheory.CompanionTheory.Ar.Plug.many_sections : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∀ ε : ℝ, 0 < ε → ∃ᶠ τ : ℕ in atTop, ∃ (n : ℕ) (f : Fin n → (T.M B b).Ω), LinearIndependent ℤ f ∧ (∀ i, ∃ R, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (τ • u) R) ∧ ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε) * (τ : ℝ) ^ (Top.dimFl (CMType H) (Dw.p + Dw.q)) ≤ ((Top.dimFl (CMType H) (Dw.p + Dw.q)).factorial : ℝ) * n := by
  intro hRR hG E _ _ _ H Dw l Xo c Y _ T o B b II u g hII hT1 hW hB ε hε
  have hanti : ∀ τ, StrictAnti (u τ) := fun τ a b' hab => by
    have := hW.2.1 τ a b' hab
    simpa [reW] using this
  obtain ⟨C, s, q, m, θ, hC, hs, hs0, hq, hm, hsm⟩ := GlobalTheory.T.strict_weight_growth_bound hG E H Dw l Xo c Y T o B b u hanti
  obtain ⟨hnef, hdeg, -, hpos⟩ := GlobalTheory.T.weight_threshold_limit_coefficients (CMType H) (Dw.p + Dw.q) T II B (reW u) g b s q m hII hT1 hW hB hs hs0
    (fun n => (hq n).1) hm
  have hD : 1 ≤ Top.dimFl (CMType H) (Dw.p + Dw.q) := by
    have h1 := T.j_pos
    have h2 := T.j_lt
    have hN : 2 ≤ Dw.p + Dw.q := by omega
    have h3 : 2 ≤ (Dw.p + Dw.q) * (Dw.p + Dw.q - 1) := by
      calc 2 = 2 * 1 := rfl
        _ ≤ _ := Nat.mul_le_mul hN (by omega)
    unfold Top.dimFl
    exact Nat.succ_le_of_lt (Nat.mul_pos (Fintype.card_pos_iff.mpr (cmType_nonempty H))
      (Nat.div_pos h3 two_pos))
  have hev := hdeg.eventually (lt_mem_nhds (show (T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε / 2 < _ by linarith))
  obtain ⟨n, hn1, hn2⟩ := (hnef.and hev).exists
  obtain ⟨P0, hP0, hsp⟩ := hn1.semipos
  have harith := (T.M B b).arith
  haveI : CharZero (T.M B b).Ω := charZero_of_arith (T.M B b).y harith
  obtain ⟨hfd, hlim⟩ := GlobalTheory.T.section_count_tendsto_geomDeg hRR hG II hII (T.M B b).K (T.M B b).ι (T.M B b).Ω (T.M B b).y
    (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)) hD harith
    (T.M B b).birational hsp.1
    (fun W _ hW' => GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.geomDeg_one_nonneg hP0 hsp hW')
  have hqn : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast (hq n).1
  have hqpos : (0 : ℝ) < (q n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) := pow_pos hqn _
  rw [lt_div_iff₀ hqpos] at hn2
  have hlt : ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε) * (q n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) <
      geomDeg (mCoordIdeal (T.M B b).y) (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n))
        (Top.dimFl (CMType H) (Dw.p + Dw.q)) := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) hqpos.le) hn2
  have hev2 := hlim.eventually (lt_mem_nhds hlt)
  rw [frequently_atTop]
  intro a
  obtain ⟨τ, hτ1, hτ2⟩ := (hev2.and (eventually_ge_atTop (a + 1))).exists
  have hτ0 : 0 < τ := by omega
  refine ⟨τ * q n, ?_, ?_⟩
  · have := Nat.le_mul_of_pos_right τ (hq n).1
    omega
  haveI := hfd τ
  obtain ⟨v, hvS, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (chartLatNm (T.M B b).y (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)).a τ : Set (T.M B b).Ω)
  refine ⟨_, fun i => v i * θ n ^ τ, indep_mul v hli (pow_ne_zero _ (hq n).2.2), fun i => ?_, ?_⟩
  · obtain ⟨C', hC', hb⟩ := bounded_section_smooth_metric (T.M B b).y _ τ (v i) hsp.1 (hvS i)
    obtain ⟨t, ht⟩ := small_shift hτ0 (hq n).1 hC' hb
    exact ⟨_, hsm n τ t (v i) (hvS i) ht⟩
  · have hτr : (0 : ℝ) < (τ : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) := pow_pos (by exact_mod_cast hτ0) _
    rw [lt_div_iff₀ hτr] at hτ1
    have e : (((τ * q n : ℕ) : ℝ)) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) =
        (q n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) * (τ : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) := by
      push_cast
      rw [mul_pow, mul_comm]
    rw [e, ← mul_assoc]
    exact hτ1.le
