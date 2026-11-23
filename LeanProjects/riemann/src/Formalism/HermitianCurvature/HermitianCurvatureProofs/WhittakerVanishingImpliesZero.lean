import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RemainderNormLeStrictUpper

open Matrix

namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero

open Formalism.FourierDecayAlt.G

theorem extendedCharacter_one {r : ℝ} (h : r ≤ 1) : chi0 r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem smooth_cutoff_eq_zero_of_two_le {r : ℝ} (h : 2 ≤ r) : chi0 r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem chi0_nonneg (r : ℝ) : 0 ≤ chi0 r := Real.smoothTransition.nonneg _

theorem smooth_cutoff_le_one (r : ℝ) : chi0 r ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_smooth_cutoff {n : ℕ∞} : ContDiff ℝ n chi0 :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem lt_two_mul_of_sq_div_lt {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) (h : a ^ 2 / τ ^ 2 < 2) :
    a < 2 * τ := by
  rw [div_lt_iff₀ (by positivity)] at h
  nlinarith

theorem cutM_nonneg {s : ℕ} (τ : ℝ) (Z : Mat s) : 0 ≤ cutM τ Z :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => chi0_nonneg _

theorem cutM_le_one {s : ℕ} (τ : ℝ) (Z : Mat s) : cutM τ Z ≤ 1 :=
  Finset.prod_le_one (fun _ _ => Finset.prod_nonneg fun _ _ => chi0_nonneg _)
    fun _ _ => Finset.prod_le_one (fun _ _ => chi0_nonneg _) fun _ _ => smooth_cutoff_le_one _

theorem cutM_eq_one {s : ℕ} {τ : ℝ} {Z : Mat s} (hτ : 0 < τ) (h : ‖Z‖ ≤ τ) : cutM τ Z = 1 := by
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => extendedCharacter_one ?_
  have h1 : ‖Z i j‖ ≤ τ := ((norm_le_pi_norm (Z i) j).trans (norm_le_pi_norm Z i)).trans h
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem cutM_eq_zero {s : ℕ} {τ : ℝ} {Z : Mat s} (hτ : 0 < τ) (h : 2 * τ ≤ ‖Z‖) : cutM τ Z = 0 := by
  by_contra hne
  have h1 : ∀ i j, ‖Z i j‖ < 2 * τ := by
    intro i j
    refine lt_two_mul_of_sq_div_lt (norm_nonneg _) hτ ?_
    by_contra hge
    exact hne (Finset.prod_eq_zero (Finset.mem_univ i)
      (Finset.prod_eq_zero (Finset.mem_univ j) (smooth_cutoff_eq_zero_of_two_le (not_lt.mp hge))))
  have h2 : ‖Z‖ < 2 * τ :=
    (pi_norm_lt_iff (by positivity)).mpr fun i => (pi_norm_lt_iff (by positivity)).mpr (h1 i)
  exact absurd h (not_le.mpr h2)

theorem cutM_contDiff {s : ℕ} (τ : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutM (s := s) τ) := by
  show ContDiff ℝ n (fun Z : Mat s => ∏ i, ∏ j, chi0 (‖Z i j‖ ^ 2 / τ ^ 2))
  refine contDiff_prod fun i _ => contDiff_prod fun j _ => contDiff_smooth_cutoff.comp ?_
  exact ((contDiff_apply_apply ℝ ℂ i j).norm_sq ℝ).div_const _

theorem cutM_scale {s : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    cutM (s := s) τ = fun Z => cutM 1 (τ⁻¹ • Z) := by
  funext Z
  unfold cutM
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  rw [Pi.smul_apply, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
  field_simp

theorem cutM_one_bound (s j : ℕ) : ∃ C : ℝ, ∀ Z : Mat s, ‖iteratedFDeriv ℝ j (cutM 1) Z‖ ≤ C := by
  have hc : HasCompactSupport (cutM (s := s) 1) :=
    HasCompactSupport.intro (isCompact_closedBall 0 2) fun Z hZ => cutM_eq_zero one_pos (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hZ
      linarith)
  exact ((cutM_contDiff 1 (n := j)).continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
    (hc.iteratedFDeriv j)

theorem common_bound {α : Type*} (k : ℕ) (f : ℕ → α → ℝ) (h : ∀ j, ∃ C : ℝ, ∀ a, f j a ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ a, f j a ≤ C := by
  choose C hC using h
  refine ⟨∑ j ∈ Finset.range (k + 1), |C j|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro j hj a
  refine ((hC j a).trans (le_abs_self _)).trans ?_
  exact Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem cutM_deriv (s k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ j ≤ k, ∀ Z : Mat s,
    ‖iteratedFDeriv ℝ j (cutM τ) Z‖ ≤ C * (τ ^ j)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := common_bound k (fun j (Z : Mat s) => ‖iteratedFDeriv ℝ j (cutM 1) Z‖)
    (cutM_one_bound s)
  refine ⟨C, hC0, fun τ hτ j hj Z => ?_⟩
  rw [cutM_scale hτ, iteratedFDeriv_comp_const_smul τ⁻¹ (cutM_contDiff 1 (n := j)), norm_smul, norm_pow,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ), inv_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC j hj _) (by positivity)

theorem critCut_nonneg {n : ℕ} (δ : ℝ) (z : ℂ) (x : Fin n → ℂ) : 0 ≤ critCut δ z x :=
  Finset.prod_nonneg fun _ _ => chi0_nonneg _

theorem critCut_le_one {n : ℕ} (δ : ℝ) (z : ℂ) (x : Fin n → ℂ) : critCut δ z x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => chi0_nonneg _) fun _ _ => smooth_cutoff_le_one _

theorem critCut_eq_one {n : ℕ} {δ : ℝ} {z : ℂ} {x : Fin n → ℂ} (hδ : 0 < δ)
    (h : ‖x - fun _ => z‖ ≤ δ) : critCut δ z x = 1 := by
  refine Finset.prod_eq_one fun k _ => extendedCharacter_one ?_
  have h1 : ‖x k - z‖ ≤ δ := (norm_le_pi_norm (x - fun _ => z) k).trans h
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem lt_of_critCut_ne_zero {n : ℕ} {δ : ℝ} {z : ℂ} {x : Fin n → ℂ} (hδ : 0 < δ)
    (h : critCut δ z x ≠ 0) (k : Fin n) : ‖x k - z‖ < 2 * δ := by
  refine lt_two_mul_of_sq_div_lt (norm_nonneg _) hδ ?_
  by_contra hge
  exact h (Finset.prod_eq_zero (Finset.mem_univ k) (smooth_cutoff_eq_zero_of_two_le (not_lt.mp hge)))

theorem critCut_eq_zero {n : ℕ} {δ : ℝ} {z : ℂ} {x : Fin n → ℂ} (hδ : 0 < δ)
    (h : 2 * δ ≤ ‖x - fun _ => z‖) : critCut δ z x = 0 := by
  by_contra hne
  have h2 : ‖x - fun _ => z‖ < 2 * δ :=
    (pi_norm_lt_iff (by positivity)).mpr fun k => lt_of_critCut_ne_zero hδ hne k
  exact absurd h (not_le.mpr h2)

theorem critCut_contDiff {d : ℕ} (δ : ℝ) (z : ℂ) {n : ℕ∞} : ContDiff ℝ n (critCut (n := d) δ z) := by
  show ContDiff ℝ n (fun x : Fin d → ℂ => ∏ k, chi0 (‖x k - z‖ ^ 2 / δ ^ 2))
  refine contDiff_prod fun k _ => contDiff_smooth_cutoff.comp ?_
  exact (((contDiff_apply ℝ ℂ k).sub contDiff_const).norm_sq ℝ).div_const _

theorem critCut_shift {d : ℕ} (δ : ℝ) (z : ℂ) :
    critCut (n := d) δ z = fun x => critCut δ 0 (x - fun _ => z) := by
  funext x
  simp [critCut]

theorem exists_norm_iteratedFDeriv_critCut_le (d : ℕ) {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    ∃ C : ℝ, ∀ x : Fin d → ℂ, ‖iteratedFDeriv ℝ j (critCut δ 0) x‖ ≤ C := by
  have hc : HasCompactSupport (critCut (n := d) δ 0) :=
    HasCompactSupport.intro (isCompact_closedBall 0 (2 * δ)) fun x hx => critCut_eq_zero hδ (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      have e : (x - fun _ => (0 : ℂ)) = x := by funext k; simp
      rw [e]
      exact hx.le)
  exact ((critCut_contDiff δ 0 (n := j)).continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
    (hc.iteratedFDeriv j)

theorem norm_pow_sub_one_le {ζ : ℂ} (h : ‖ζ‖ = 1) (i : ℕ) : ‖ζ ^ i - 1‖ ≤ i * ‖ζ - 1‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : ζ ^ (i + 1) - 1 = ζ * (ζ ^ i - 1) + (ζ - 1) := by ring
    rw [e]
    calc ‖ζ * (ζ ^ i - 1) + (ζ - 1)‖ ≤ ‖ζ * (ζ ^ i - 1)‖ + ‖ζ - 1‖ := norm_add_le _ _
      _ = ‖ζ ^ i - 1‖ + ‖ζ - 1‖ := by rw [norm_mul, h, one_mul]
      _ ≤ _ := by push_cast; linarith

theorem one_le_mul_of_root {s : ℕ} {ζ : ℂ} (hs : 0 < s) (h : ζ ^ s = 1) (hne : ζ ≠ 1) :
    1 ≤ (s : ℝ) * ‖ζ - 1‖ := by
  have hn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h hs.ne'
  have hsum : ∑ i ∈ Finset.range s, ζ ^ i = 0 := by
    have := mul_geom_sum ζ s
    rw [h, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have h1 : ∑ i ∈ Finset.range s, (ζ ^ i - 1) = -(s : ℂ) := by
    rw [Finset.sum_sub_distrib, hsum]; simp
  have h2 : (s : ℝ) ≤ ∑ _i ∈ Finset.range s, (s : ℝ) * ‖ζ - 1‖ := by
    calc (s : ℝ) = ‖-(s : ℂ)‖ := by simp
      _ = ‖∑ i ∈ Finset.range s, (ζ ^ i - 1)‖ := by rw [h1]
      _ ≤ ∑ i ∈ Finset.range s, ‖ζ ^ i - 1‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun i hi => (norm_pow_sub_one_le hn i).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hi).le) (norm_nonneg _))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  exact le_of_mul_le_mul_left (by linarith) hs'

theorem root_sep {s : ℕ} (hs : 0 < s) {z z' : ℂ} (h : z ^ s = z' ^ s) (hne : z ≠ z') :
    ‖z‖ ≤ (s : ℝ) * ‖z - z'‖ := by
  by_cases hz : z = 0
  · rw [hz, norm_zero]; positivity
  have h1 : (z' / z) ^ s = 1 := by rw [div_pow, ← h, div_self (pow_ne_zero _ hz)]
  have h2 : z' / z ≠ 1 := by
    intro e
    exact hne ((div_eq_one_iff_eq hz).mp e).symm
  have h3 := one_le_mul_of_root hs h1 h2
  have e : z - z' = -(z * (z' / z - 1)) := by field_simp; ring
  rw [e, norm_neg, norm_mul]
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  nlinarith

theorem exists_lower {Kc : Set ℂ} (hK : IsCompact Kc) (h0 : (0 : ℂ) ∉ Kc) :
    ∃ d : ℝ, 0 < d ∧ ∀ D ∈ Kc, d ≤ ‖D‖ := by
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl 0 h0
  refine ⟨d, hd, fun D hDK => ?_⟩
  by_contra hlt
  exact hball (by simpa [Metric.mem_ball] using not_le.mp hlt) hDK

theorem norm_iteratedFDeriv_smul_le_at {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} {g : E → F} {x : E} {n : ℕ}
    (hf : ContDiff ℝ n f) (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  obtain ⟨u, hu, hxu, hgu⟩ := ContDiffWithinAt.contDiffOn' (m := n) (s := Set.univ) le_rfl (by simp)
    hg.contDiffWithinAt
  have hgu' : ContDiffOn ℝ n g u := by simpa using hgu
  have key := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (𝕜' := ℝ) (N := n) hf.contDiffOn hgu' hu.uniqueDiffOn hxu
    (n := n) le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hu hxu] at key
  refine key.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [iteratedFDerivWithin_of_isOpen i hu hxu, iteratedFDerivWithin_of_isOpen (n - i) hu hxu]

end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6 Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero

theorem matrix_cutoff_spec : Formalism.FourierDecayAlt.G.CutMSpec := by
  intro s
  refine ⟨fun τ Z hτ => ⟨cutM_nonneg τ Z, cutM_le_one τ Z, cutM_eq_one hτ, cutM_eq_zero hτ⟩, fun k => ?_⟩
  obtain ⟨C, _, hC⟩ := cutM_deriv s k
  exact ⟨C, fun τ hτ => ⟨cutM_contDiff τ (n := k), hC τ hτ⟩⟩

theorem critical_cutoff_spec : Formalism.FourierDecayAlt.G.CritCutSpec := by
  intro m δ hδ
  refine ⟨fun z x => ⟨critCut_nonneg δ z x, critCut_le_one δ z x, critCut_eq_one hδ, critCut_eq_zero hδ⟩,
    fun k => ?_, ?_⟩
  · obtain ⟨C, _, hC⟩ := common_bound k
      (fun j (x : Fin (m + 1) → ℂ) => ‖iteratedFDeriv ℝ j (critCut δ 0) x‖) (exists_norm_iteratedFDeriv_critCut_le (m + 1) hδ)
    refine ⟨C, fun z => ⟨critCut_contDiff δ z (n := k), fun j hj x => ?_⟩⟩
    rw [critCut_shift δ z, iteratedFDeriv_comp_sub]
    exact hC j hj _
  · intro z z' x hzz hne hz hx
    have h1 : ‖x 0 - z‖ < 2 * δ := lt_of_critCut_ne_zero hδ hx 0
    have h2 : ‖z‖ ≤ ((m + 2 : ℕ) : ℝ) * ‖z - z'‖ := root_sep (by omega) hzz hne
    push_cast at h2
    have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have h3 : 100 * δ ≤ ‖z - z'‖ := by
      have : ((m : ℝ) + 2) * (100 * δ) ≤ ((m : ℝ) + 2) * ‖z - z'‖ := by linarith
      exact le_of_mul_le_mul_left this hm
    have h4 : ‖z - z'‖ ≤ ‖x 0 - z‖ + ‖x 0 - z'‖ := by
      have e : z - z' = -(x 0 - z) + (x 0 - z') := by ring
      rw [e]
      exact (norm_add_le _ _).trans (by rw [norm_neg])
    have h5 : 2 * δ ≤ ‖x 0 - z'‖ := by linarith
    refine Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (m + 1))) (smooth_cutoff_eq_zero_of_two_le ?_)
    rw [le_div_iff₀ (by positivity)]
    nlinarith

theorem cutoff_phase_bound : Formalism.FourierDecayAlt.G.CutPhiBound := by
  intro s k
  obtain ⟨C0, hC0, hcut⟩ := cutM_deriv s k
  refine ⟨1 + 2 ^ k * C0, ?_⟩
  intro V _ _ Φ Kd bd τ hτ hΦ
  have hτ0 : 0 < τ := lt_of_lt_of_le one_pos hτ
  have e1 : cutPhi τ Φ = fun Z => cutM τ Z • Φ Z := by
    funext Z
    exact Complex.coe_smul _ _
  have e2 : cutPhiC τ Φ = Φ - cutPhi τ Φ := by
    funext Z
    simp only [cutPhiC, cutPhi, Pi.sub_apply]
    push_cast
    rw [sub_smul, one_smul]
  have hbd : ∀ Z, detM Z ∈ Kd → 0 ≤ bd Z := fun Z hZ =>
    (norm_nonneg _).trans ((hΦ Z hZ).2 0 (Nat.zero_le _))
  have hsm : ∀ Z, detM Z ∈ Kd → ContDiffAt ℝ k (cutPhi τ Φ) Z := by
    intro Z hZ
    rw [e1]
    exact (cutM_contDiff τ (n := k)).contDiffAt.smul (hΦ Z hZ).1
  have key : ∀ Z, detM Z ∈ Kd → ∀ j ≤ k, ‖iteratedFDeriv ℝ j (cutPhi τ Φ) Z‖ ≤ 2 ^ k * C0 * bd Z := by
    intro Z hZ j hj
    have hjk : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((k : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj
    rw [e1]
    refine (norm_iteratedFDeriv_smul_le_at (cutM_contDiff τ (n := j)) ((hΦ Z hZ).1.of_le hjk)).trans ?_
    calc ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutM τ) Z‖ * ‖iteratedFDeriv ℝ (j - i) Φ Z‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (C0 * bd Z) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ k := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hj
          have h1 : ‖iteratedFDeriv ℝ i (cutM τ) Z‖ ≤ C0 := by
            refine (hcut τ hτ0 i hi' Z).trans ?_
            have : (τ ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hτ)
            nlinarith
          have h2 : ‖iteratedFDeriv ℝ (j - i) Φ Z‖ ≤ bd Z := (hΦ Z hZ).2 _ ((Nat.sub_le _ _).trans hj)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hC0) (Nat.cast_nonneg _)
      _ = 2 ^ j * (C0 * bd Z) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ k * (C0 * bd Z) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hj) (mul_nonneg hC0 (hbd Z hZ))
      _ = 2 ^ k * C0 * bd Z := by ring
  constructor
  · intro Z hZ
    refine ⟨hsm Z hZ, fun j hj => (key Z hZ j hj).trans ?_⟩
    have := hbd Z hZ
    nlinarith
  · intro Z hZ
    rw [e2]
    refine ⟨(hΦ Z hZ).1.sub (hsm Z hZ), fun j hj => ?_⟩
    have hjk : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((k : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast hj
    rw [iteratedFDeriv_sub_apply ((hΦ Z hZ).1.of_le hjk) ((hsm Z hZ).of_le hjk)]
    refine (norm_sub_le _ _).trans ?_
    have h1 := (hΦ Z hZ).2 j hj
    have h2 := key Z hZ j hj
    linarith

theorem exists_small_delta : Formalism.FourierDecayAlt.G.SmallDeltaExists := by
  intro m Kc hK h0
  obtain ⟨d, hd, hD⟩ := exists_lower hK h0
  have hm : (0 : ℝ) < 100 * ((m : ℝ) + 2) := by positivity
  refine ⟨min 1 d / (100 * ((m : ℝ) + 2)), by positivity, fun D hDK z hz => ?_⟩
  rw [mul_div_cancel₀ _ hm.ne']
  by_contra hlt
  rw [not_le, lt_min_iff] at hlt
  have h1 : ‖z‖ ^ (m + 2) = ‖D‖ := by
    rw [← norm_pow, hz, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have h2 : ‖z‖ ^ (m + 2) ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg _) hlt.1.le (by omega)
  have h3 := hD D hDK
  linarith [hlt.2]

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6

theorem norm_xOf_le {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {B : Fin (m + 1) → ℂ} {L : ℝ}
    (hX : ∀ i j, ‖X i j‖ ≤ L) (hB : ∀ i, ‖B i‖ ≤ L) (k : Fin (m + 1)) : ‖xOf X B k‖ ≤ L := by
  refine Fin.lastCases ?_ (fun k => ?_) k
  · rw [xOf_last]; exact hB _
  · rw [xOf_castSucc]; exact hX _ _

theorem cof_split {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hS : IsStrictUpper X)
    (B : Fin (m + 1) → ℂ) (t : ℂ) :
    Cof X B t = (∑ j ∈ Finset.range m, ((-X) ^ j *ᵥ B) 0 * t ^ (m - j)) + (-1) ^ m * ∏ k, xOf X B k := by
  have h := (Formalism.FourierDecayAlt.P.leading_cofactor m X B 0 hS).1
  rw [Cof, sum_mul_zero_pow m (fun j => ((-X) ^ j *ᵥ B) 0)] at h
  rw [Cof, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, h]

theorem norm_cof_rest_le {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} {B : Fin (m + 1) → ℂ}
    {t : ℂ} {L : ℝ} (hL : 1 ≤ L) (ht : ‖t‖ ≤ 1) (hX : ∀ i j, ‖X i j‖ ≤ L) (hB : ∀ i, ‖B i‖ ≤ L) :
    ‖∑ j ∈ Finset.range m, ((-X) ^ j *ᵥ B) 0 * t ^ (m - j)‖ ≤
      ((m : ℝ) * ((m : ℝ) + 1) ^ m) * (L ^ (m + 1) * ‖t‖) := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  calc ‖∑ j ∈ Finset.range m, ((-X) ^ j *ᵥ B) 0 * t ^ (m - j)‖
      ≤ ∑ j ∈ Finset.range m, ‖((-X) ^ j *ᵥ B) 0 * t ^ (m - j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range m, (((m : ℝ) + 1) ^ m * L ^ (m + 1)) * ‖t‖ := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        rw [norm_mul, norm_pow]
        refine mul_le_mul ((norm_pow_mulVec_le hL0 hX hB j 0).trans ?_)
          (pow_le_of_le_one (norm_nonneg _) ht (by omega)) (by positivity) (by positivity)
        exact mul_le_mul (pow_le_pow_right₀ hm1 hj'.le) (pow_le_pow_right₀ hL (by omega))
          (by positivity) (by positivity)
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6 Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero

theorem product_lower_bound : Formalism.FourierDecayAlt.G.ProdLower := by
  intro m Kc hK h0 R hR
  obtain ⟨d, hd, hD⟩ := exists_lower hK h0
  set R' : ℝ := max R 1 with hR'
  have hR1 : 1 ≤ R' := le_max_right _ _
  have hR0 : 0 < R' := lt_of_lt_of_le one_pos hR1
  set Cm : ℝ := ((m : ℝ) + 1) * ((m : ℝ) * ((m : ℝ) + 1) ^ m) with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set Ce : ℝ := (m : ℝ) * ((m : ℝ) + 1) ^ m with hCe
  have hCe0 : 0 ≤ Ce := by positivity
  set q : ℝ := d / (2 * (Cm + Ce + 1) * R' ^ (m + 2)) with hq
  have hq0 : 0 < q := by positivity
  refine ⟨min 1 (q ^ 2), d / (2 * R' ^ (m + 1)), by positivity, by positivity, ?_⟩
  intro ε hε hε2 D hDK t ht htle X B ρ₁ ρ' σ hS hX hB hρ₁ hρ' hσ hrel
  have hT : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hT1 : ‖t‖ ≤ 1 := le_trans htle (min_le_left _ _)
  have hTq : ‖t‖ ≤ q ^ 2 := le_trans htle (min_le_right _ _)
  set W : ℝ := ‖t‖ ^ (-ε) with hW
  have hW1 : 1 ≤ W := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hT hT1 (by linarith)
  have hW0 : 0 < W := lt_of_lt_of_le one_pos hW1
  set L : ℝ := R' * W with hLdef
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le hR1 hW1
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hRL : R * W ≤ L := mul_le_mul_of_nonneg_right (le_max_left _ _) hW0.le
  have hX' : ∀ i j, ‖X i j‖ ≤ L := fun i j => (hX i j).trans hRL
  have hB' : ∀ i, ‖B i‖ ≤ L := fun i => (hB i).trans hRL
  have hρ'' : ∀ k, ‖ρ' k‖ ≤ L := fun k => (hρ' k).trans hRL
  have hsq : L ^ (m + 2) * ‖t‖ ≤ R' ^ (m + 2) * q := by
    rw [hLdef, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (le_trans (rpow_bound m hT hT1 hε2) (Real.sqrt_le_iff.mpr ⟨hq0.le, hTq⟩)) (by positivity)
  have hRb := remainder_norm_le_strict_upper (t := t) hL hT1 hS hX' hB' hρ''
  set P : ℂ := ∏ k, xOf X B k with hP
  set E : ℂ := ∑ j ∈ Finset.range m, ((-X) ^ j *ᵥ B) 0 * t ^ (m - j) with hE
  have hCof : Cof X B t = E + (-1) ^ m * P := cof_split hS B t
  have hEb : ‖E‖ ≤ Ce * (L ^ (m + 1) * ‖t‖) := norm_cof_rest_le hL hT1 hX' hB'
  have hEρ : ‖E * ρ₁‖ ≤ Ce * (L ^ (m + 2) * ‖t‖) := by
    rw [norm_mul]
    calc ‖E‖ * ‖ρ₁‖ ≤ (Ce * (L ^ (m + 1) * ‖t‖)) * L :=
          mul_le_mul hEb (hρ₁.trans hRL) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h1 : ‖t ^ (m + 1) * σ‖ ≤ L ^ (m + 2) * ‖t‖ := by
    rw [norm_mul, norm_pow, mul_comm]
    refine mul_le_mul (le_trans (hσ.trans hRL) (le_self_pow₀ hL (by omega)))
      (pow_le_of_le_one hT.le hT1 (by omega)) (by positivity) (by positivity)
  have h2 : ‖(-1) ^ m * P * ρ₁‖ ≤ ‖P‖ * L := by
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact mul_le_mul_of_nonneg_left (hρ₁.trans hRL) (norm_nonneg _)
  have hDeq : D = t ^ (m + 1) * σ - (-1) ^ m * P * ρ₁ - E * ρ₁ - R0 X B ρ' t := by
    rw [hrel, hCof]; ring
  have h3 : ‖D‖ ≤ L ^ (m + 2) * ‖t‖ + ‖P‖ * L + Ce * (L ^ (m + 2) * ‖t‖) + Cm * (L ^ (m + 2) * ‖t‖) := by
    calc ‖D‖ = ‖t ^ (m + 1) * σ - (-1) ^ m * P * ρ₁ - E * ρ₁ - R0 X B ρ' t‖ := by rw [← hDeq]
      _ ≤ ‖t ^ (m + 1) * σ‖ + ‖(-1) ^ m * P * ρ₁‖ + ‖E * ρ₁‖ + ‖R0 X B ρ' t‖ := by
          refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
          refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
          exact norm_sub_le _ _
      _ ≤ _ := add_le_add (add_le_add (add_le_add h1 h2) hEρ) hRb
  have h4 : (Cm + Ce + 1) * (L ^ (m + 2) * ‖t‖) ≤ d / 2 := by
    calc (Cm + Ce + 1) * (L ^ (m + 2) * ‖t‖) ≤ (Cm + Ce + 1) * (R' ^ (m + 2) * q) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = d / 2 := by rw [hq]; field_simp
  have h5 : d / 2 ≤ ‖P‖ * L := by
    have := hD D hDK
    linarith
  have hRpow : 0 < R' ^ (m + 1) := by positivity
  constructor
  · have hinv : ‖t‖ ^ ε = W⁻¹ := by rw [hW, Real.rpow_neg hT.le, inv_inv]
    rw [hinv, ← div_eq_mul_inv, div_le_iff₀ hW0, div_le_iff₀ (by positivity)]
    have h6 : R' ≤ R' ^ (m + 1) := le_self_pow₀ hR1 (by omega)
    have h7 : ‖P‖ * L ≤ ‖P‖ * W * R' ^ (m + 1) := by
      rw [hLdef, mul_assoc, mul_comm R' W]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h6 hW0.le) (norm_nonneg _)
    linarith
  · intro k
    have h6 : ‖P‖ ≤ ‖xOf X B k‖ * L ^ m := by
      rw [hP, ← Finset.mul_prod_erase Finset.univ (fun k => xOf X B k) (Finset.mem_univ k), norm_mul,
        norm_prod]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ∏ l ∈ Finset.univ.erase k, ‖xOf X B l‖ ≤ ∏ _l ∈ Finset.univ.erase k, L :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun l _ => norm_xOf_le hX' hB' l
        _ = L ^ m := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
              Fintype.card_fin, Nat.add_sub_cancel]
    have h7 : d / 2 ≤ ‖xOf X B k‖ * (R' ^ (m + 1) * W ^ (m + 1)) := by
      calc d / 2 ≤ ‖P‖ * L := h5
        _ ≤ ‖xOf X B k‖ * L ^ m * L := mul_le_mul_of_nonneg_right h6 hL0.le
        _ = _ := by rw [hLdef]; ring
    have h8 : ‖t‖ ^ (((m : ℝ) + 2) * ε) ≤ (W ^ (m + 1))⁻¹ := by
      have e : (W ^ (m + 1))⁻¹ = ‖t‖ ^ (((m : ℝ) + 1) * ε) := by
        rw [hW, ← Real.rpow_natCast, ← Real.rpow_mul hT.le, ← Real.rpow_neg hT.le]
        congr 1
        push_cast
        ring
      rw [e]
      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (mul_le_mul_of_nonneg_right (by linarith) hε.le)
    have hWp : 0 < W ^ (m + 1) := by positivity
    calc d / (2 * R' ^ (m + 1)) * ‖t‖ ^ (((m : ℝ) + 2) * ε)
        ≤ d / (2 * R' ^ (m + 1)) * (W ^ (m + 1))⁻¹ := mul_le_mul_of_nonneg_left h8 (by positivity)
      _ ≤ ‖xOf X B k‖ := by
          rw [← div_eq_mul_inv, div_le_iff₀ hWp, div_le_iff₀ (by positivity)]
          linarith

end Formalism.FourierDecayAlt.P
