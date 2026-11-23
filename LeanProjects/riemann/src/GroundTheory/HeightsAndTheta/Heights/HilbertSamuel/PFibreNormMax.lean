import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormMax
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedG
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormMax

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem isMultiHomog_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero =>
    intro m hm k
    rw [pow_zero, MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul ih hf

theorem exists_lower {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {m : ℕ} (e : K → ℕ)
    (L : Fin m → MRing ι) (hL : ∀ j, IsMultiHomog (L j) e)
    (h0 : ∀ z ∈ mcPts P, ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ mcPts P,
      δ * ∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ e k ≤ ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖ := by
  let φ : ((Σ k, ι k) → ℂ) → ℝ := fun z => ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖
  have hφc : Continuous φ := (continuous_pi fun j => MvPolynomial.continuous_eval _).norm
  let T : Set ((Σ k, ι k) → ℂ) :=
    {z | ∀ k, ‖(fun i => z ⟨k, i⟩)‖ = 1} ∩ ⋂ f ∈ (P : Set (MRing ι)), {z | eval z (map (Int.castRingHom ℂ) f) = 0}
  have hTc : IsCompact T := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · refine IsClosed.inter ?_ (isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _)
        continuous_const)
      have hS : {z : (Σ k, ι k) → ℂ | ∀ k, ‖(fun i => z ⟨k, i⟩)‖ = 1} =
          ⋂ k, (fun z : (Σ k, ι k) → ℂ => ‖(fun i => z ⟨k, i⟩)‖) ⁻¹' {1} := by
        ext z; simp
      rw [hS]
      exact isClosed_iInter fun k => isClosed_singleton.preimage
        (continuous_pi fun i => continuous_apply _).norm
    · refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro p
      calc ‖z p‖ = ‖(fun i => z ⟨p.1, i⟩) p.2‖ := rfl
        _ ≤ ‖(fun i => z ⟨p.1, i⟩)‖ := norm_le_pi_norm (fun i => z ⟨p.1, i⟩) p.2
        _ = 1 := hz.1 p.1
  have hTP : T ⊆ mcPts P := by
    intro z hz
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · by_contra h
      simp only [not_exists, not_not] at h
      have h1 : ‖(fun i => z ⟨k, i⟩)‖ = 1 := hz.1 k
      rw [show (fun i => z ⟨k, i⟩) = 0 from funext h, norm_zero] at h1
      exact zero_ne_one h1
    · exact Set.mem_iInter₂.mp hz.2 f hf
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ T, δ ≤ φ w := by
    rcases T.eq_empty_or_nonempty with hT | hT
    · exact ⟨1, one_pos, fun w hw => by rw [hT] at hw; exact hw.elim⟩
    obtain ⟨w0, hw0, hmin⟩ := hTc.exists_isMinOn hT hφc.continuousOn
    obtain ⟨j, hj⟩ := h0 w0 (hTP hw0)
    exact ⟨φ w0, (norm_pos_iff.mpr hj).trans_le (norm_le_pi_norm (fun j =>
      eval w0 (map (Int.castRingHom ℂ) (L j))) j), fun w hw => hmin hw⟩
  obtain ⟨δ, hδ0, hδT⟩ := hδ
  refine ⟨δ, hδ0, fun z hz => ?_⟩
  have hn : ∀ k, 0 < ‖(fun i => z ⟨k, i⟩)‖ := fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    exact norm_pos_iff.mpr fun h => hi (congrFun h i)
  let c : K → ℂ := fun k => ((‖(fun i => z ⟨k, i⟩)‖⁻¹ : ℝ) : ℂ)
  have hc0 : ∀ k, c k ≠ 0 := fun k => by
    simp only [c, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (hn k).ne'
  have hcn : ∀ k, ‖c k‖ = ‖(fun i => z ⟨k, i⟩)‖⁻¹ := fun k => by
    simp only [c, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (inv_pos.mpr (hn k))
  have hwT : (fun p : Σ k, ι k => c p.1 * z p) ∈ T := by
    refine ⟨fun k => ?_, Set.mem_iInter₂.mpr fun f hf => (mcPts_smul hP c hc0 hz).2 f hf⟩
    have h1 : (fun i => (fun p : Σ k, ι k => c p.1 * z p) ⟨k, i⟩) = c k • (fun i => z ⟨k, i⟩) := rfl
    show ‖(fun i => (fun p : Σ k, ι k => c p.1 * z p) ⟨k, i⟩)‖ = 1
    rw [h1, norm_smul, hcn, inv_mul_cancel₀ (hn k).ne']
  have hφw : φ (fun p : Σ k, ι k => c p.1 * z p) = (∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ e k)⁻¹ * φ z := by
    have h1 : (fun j => eval (fun p : Σ k, ι k => c p.1 * z p) (map (Int.castRingHom ℂ) (L j))) =
        (∏ k, c k ^ e k) • fun j => eval z (map (Int.castRingHom ℂ) (L j)) := by
      funext j
      rw [eval_smul_homog (L j) e (hL j) c z]
      rfl
    show ‖(fun j => eval (fun p : Σ k, ι k => c p.1 * z p) (map (Int.castRingHom ℂ) (L j)))‖ = _
    rw [h1, norm_smul, norm_prod]
    simp only [norm_pow, hcn, inv_pow, Finset.prod_inv_distrib]
    rfl
  have hprod : 0 < ∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ e k := Finset.prod_pos fun k _ => pow_pos (hn k) _
  have h2 := hδT _ hwT
  rw [hφw] at h2
  have h3 := (le_inv_mul_iff₀ hprod).mp h2
  calc δ * ∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ e k = (∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ e k) * δ := mul_comm _ _
    _ ≤ φ z := h3

theorem exists_comparison {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {m : ℕ} (e : K → ℕ)
    (L : Fin m → MRing ι) (hL : ∀ j, IsMultiHomog (L j) e)
    (h0 : ∀ z ∈ mcPts P, ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0)
    (a : K → ℤ) (q : ℕ) (b : K → ℕ) (hb : ∀ k, (b k : ℤ) = q * e k - a k) (i : ∀ k, ι k) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z ∈ mcPts P,
      (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) a).h z * ‖eval z (map (Int.castRingHom ℂ) (secOf i b))‖ ≤
        C * ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖ ^ q := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_lower hP e L hL h0
  refine ⟨max 1 (δ⁻¹ ^ q), le_max_left _ _, fun z hz => ?_⟩
  have hn : ∀ k, 0 < ‖(fun i => z ⟨k, i⟩)‖ := fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    exact norm_pos_iff.mpr fun h => hi (congrFun h i)
  have hh0 : (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) a).h z = ∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ a k := rfl
  have hW : ‖eval z (map (Int.castRingHom ℂ) (secOf i b))‖ ≤ ∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ b k := by
    simp only [secOf, map_prod, map_pow, map_X, eval_X, norm_prod, norm_pow]
    exact Finset.prod_le_prod (fun k _ => pow_nonneg (norm_nonneg _) _) fun k _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm (fun i => z ⟨k, i⟩) (i k)) _
  have hk : ∀ k, ‖(fun i => z ⟨k, i⟩)‖ ^ a k * ‖(fun i => z ⟨k, i⟩)‖ ^ b k =
      (‖(fun i => z ⟨k, i⟩)‖ ^ e k) ^ q := fun k => by
    rw [← zpow_natCast _ (b k), ← zpow_add₀ (hn k).ne', ← pow_mul,
      show a k + (b k : ℤ) = ((e k * q : ℕ) : ℤ) by push_cast; linarith [hb k], zpow_natCast]
  have hprod : (∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ a k) * ∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ b k =
      (∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ e k) ^ q := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun k _ => hk k, Finset.prod_pow]
  have hh0n : 0 ≤ ∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ a k := Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
  have hE : ∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ e k ≤ δ⁻¹ * ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖ := by
    rw [le_inv_mul_iff₀ hδ0]
    exact hδ z hz
  have hE0 : 0 ≤ ∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ e k := Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _
  calc (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) a).h z * ‖eval z (map (Int.castRingHom ℂ) (secOf i b))‖
      ≤ (∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ a k) * ∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ b k := by
        rw [hh0]; exact mul_le_mul_of_nonneg_left hW hh0n
    _ = (∏ k, ‖(fun i => z ⟨k, i⟩)‖ ^ e k) ^ q := hprod
    _ ≤ (δ⁻¹ * ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖) ^ q := pow_le_pow_left₀ hE0 hE _
    _ = δ⁻¹ ^ q * ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖ ^ q := mul_pow _ _ _
    _ ≤ max 1 (δ⁻¹ ^ q) * ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖ ^ q :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (norm_nonneg _) _)

theorem proof (h : FibreNormPullback.Statement) : FibreNormMax.Statement := by
  intro K _ ι _ Ω _ y D a e L hV hB he hL hL0
  classical
  have hP : IsMultiHomogIdeal (mCoordIdeal y) := hV.2.1.2.1

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    simp [mCoordIdeal, mConeMap, RingHom.mem_ker, h0]
  choose i hi using hrel
  let q : ℕ := ∑ k, (a k).toNat
  let b : K → ℕ := fun k => ((q * e k : ℤ) - a k).toNat
  have hb : ∀ k, (b k : ℤ) = q * e k - a k := fun k => by
    have h1 : a k ≤ (a k).toNat := Int.self_le_toNat _
    have h2 : (a k).toNat ≤ q :=
      Finset.single_le_sum (f := fun k => (a k).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h3 : q ≤ q * e k := Nat.le_mul_of_pos_right q (he k)
    have h4 : ((a k).toNat : ℤ) ≤ ((q * e k : ℕ) : ℤ) := by exact_mod_cast h2.trans h3
    push_cast at h4
    exact Int.toNat_of_nonneg (by linarith)
  let W : MRing ι := secOf i b
  have hWy : aeval y W = ∏ k, y ⟨k, i k⟩ ^ b k := by simp [W, secOf]
  have hWy0 : aeval y W ≠ 0 := by
    rw [hWy]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hi k)
  obtain ⟨n, M₀, hn, hM₀, hF⟩ := h K ι Ω y D e L q hV hB he hL hL0
  obtain ⟨C, hC, hCz⟩ := exists_comparison hP e L hL hL0 a q b hb i
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hM₀0 : (0 : ℝ) ≤ M₀ := zero_le_one.trans hM₀
  refine ⟨n, n * q, M₀ * C ^ n, hn, one_le_mul_of_one_le_of_one_le hM₀ (one_le_pow₀ hC), ?_⟩
  intro τ u hu hu0

  have hs : u * aeval y W ^ τ ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ := by
    intro c hc
    have hgen : ∀ k, y ⟨k, i k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c := fun k => by
      show y ⟨k, i k⟩ / y ⟨k, c k⟩ ∈ Algebra.adjoin ℤ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
      exact Algebra.subset_adjoin ⟨⟨k, i k⟩, rfl⟩
    have hr : (∏ k, (y ⟨k, i k⟩ / y ⟨k, c k⟩) ^ b k) ^ τ ∈ chartRingZ y c :=
      pow_mem (prod_mem fun k _ => pow_mem (hgen k) _) _
    have hk : ∀ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) =
        y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) * ((y ⟨k, c k⟩ ^ b k) ^ τ)⁻¹ := fun k => by
      rw [← pow_mul, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hc k)]
      congr 1
      push_cast
      linear_combination (τ : ℤ) * hb k
    have key : u * aeval y W ^ τ * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) =
        (u * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) * (∏ k, (y ⟨k, i k⟩ / y ⟨k, c k⟩) ^ b k) ^ τ := by
      rw [hWy, Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib]
      simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib,
        inv_pow]
      ring
    rw [key]
    exact mul_mem (hu c hc) (Subalgebra.algebraMap_mem (integralClosure (chartRingZ y c) Ω)
      (⟨_, hr⟩ : chartRingZ y c))
  obtain ⟨F, hF0, hFh, hFb⟩ := hF τ _ hs (mul_ne_zero hu0 (pow_ne_zero _ hWy0))
  refine ⟨F, hF0, fun j => ?_, fun ζ hζ S hS M hM hrep => ?_⟩
  · calc F.degreeOf j ≤ F.totalDegree := degreeOf_le_totalDegree F j
      _ ≤ n * q * τ := hFh.totalDegree_le
      _ ≤ n * q * (τ + 1) := Nat.mul_le_mul_left _ (Nat.le_succ τ)
  have hζ0 : ζ ≠ 0 := fun h0 => by
    have h1 := hζ 0
    rw [h0, Pi.zero_apply, norm_zero] at h1
    exact zero_ne_one h1
  have hζ1 : ‖ζ‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => (hζ j).le
  have hMC : 0 ≤ M * C ^ τ := mul_nonneg hM (pow_nonneg hC0 _)
  have key := hFb ζ hζ0 S hS (M * C ^ τ) hMC (fun z hzS hz => by
    obtain ⟨dg, dh, g, h, hg, hh, hd, hgh, hz0, hle⟩ := hrep z hzS
    refine ⟨dg + τ • b, dh, g * W ^ τ, h, isMultiHomog_mul hg (isMultiHomog_pow (isMultiHomog_secOf i b) τ), hh,
      fun k => ?_, ?_, hz0, ?_⟩
    · show dg k + τ • b k = dh k + τ * (q * e k)
      rw [smul_eq_mul]
      have h1 : ((dg k + τ * b k : ℕ) : ℤ) = ((dh k + τ * (q * e k) : ℕ) : ℤ) := by
        push_cast
        linear_combination hd k + (τ : ℤ) * hb k
      exact_mod_cast h1
    · rw [map_mul, map_pow, hgh]
      ring
    · have hcz := hCz z hz
      have hh0 : 0 ≤ (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) a).h z :=
        ((HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) a).pos z hz.1).le
      simp only [map_mul, map_pow, norm_mul, norm_pow]
      calc ‖eval z (map (Int.castRingHom ℂ) g)‖ * ‖eval z (map (Int.castRingHom ℂ) W)‖ ^ τ
          ≤ (M * (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) a).h z ^ τ *
              ‖eval z (map (Int.castRingHom ℂ) h)‖) * ‖eval z (map (Int.castRingHom ℂ) W)‖ ^ τ :=
            mul_le_mul_of_nonneg_right hle (pow_nonneg (norm_nonneg _) _)
        _ = M * ((HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) a).h z *
              ‖eval z (map (Int.castRingHom ℂ) W)‖) ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖ := by ring
        _ ≤ M * (C * ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖ ^ q) ^ τ *
              ‖eval z (map (Int.castRingHom ℂ) h)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (mul_nonneg hh0 (norm_nonneg _)) hcz τ) hM) (norm_nonneg _)
        _ = M * C ^ τ * ‖fun j => eval z (map (Int.castRingHom ℂ) (L j))‖ ^ (q * τ) *
              ‖eval z (map (Int.castRingHom ℂ) h)‖ := by
            rw [mul_pow, ← pow_mul]
            ring)
  have hτn : τ * n ≤ n * (τ + 1) := by
    rw [Nat.mul_comm n]
    exact Nat.mul_le_mul_right n (Nat.le_succ τ)
  calc ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ M₀ ^ τ * ‖ζ‖ ^ (n * q * τ) * (M * C ^ τ) ^ n := key
    _ ≤ M₀ ^ τ * 1 * (M * C ^ τ) ^ n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hζ1)
          (pow_nonneg hM₀0 _)) (pow_nonneg hMC _)
    _ = M₀ ^ τ * C ^ (τ * n) * M ^ n := by
        rw [mul_pow, ← pow_mul]
        ring
    _ ≤ M₀ ^ (τ + 1) * C ^ (n * (τ + 1)) * M ^ n :=
        mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_right₀ hM₀ (Nat.le_succ τ))
          (pow_le_pow_right₀ hC hτn) (pow_nonneg hC0 _) (pow_nonneg hM₀0 _)) (pow_nonneg hM _)
    _ = (M₀ * C ^ n) ^ (τ + 1) * M ^ n := by
        rw [mul_pow, ← pow_mul]

end FibreNormMax

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
