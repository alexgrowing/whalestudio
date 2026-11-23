import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MConeMapOverBaseRename
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

noncomputable section

section Loc

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {K' : Type} [Field K'] [Algebra k K']
  {N : ℕ} {x : Fin (N + 1) → Ω} {x' : Fin (N + 1) → K'}
  (hsp : Kleiman.primeOf (S := k) x ≤ Kleiman.primeOf (S := k) x')
include hsp

theorem locAt_ratio {c : Fin (N + 1)} (hc : x' c ≠ 0) (a : Fin (N + 1)) :
    x a / x c ∈ Kleiman.locAt k x x' ∧ Kleiman.redAt k x x' (x a / x c) = x' a / x' c := by
  have hsy : aeval x' (X c : Kleiman.Poly k N) ≠ 0 := by rw [aeval_X]; exact hc
  have h1 := Kleiman.mem_locAt (x := x) (isHomogeneous_X k a) (isHomogeneous_X k c) hsy
  have h2 := Kleiman.redAt_eq hsp (isHomogeneous_X k a) (isHomogeneous_X k c) hsy
  simp only [aeval_X] at h1 h2
  exact ⟨h1, h2⟩

theorem locAt_zpow {a : Ω} (ha : a ∈ Kleiman.locAt k x x') (hr : Kleiman.redAt k x x' a ≠ 0) (n : ℤ) :
    a ^ n ∈ Kleiman.locAt k x x' ∧ Kleiman.redAt k x x' (a ^ n) = Kleiman.redAt k x x' a ^ n := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa only [zpow_natCast] using Kleiman.locAt_pow hsp ha n
  · have hp := Kleiman.locAt_pow hsp ha n
    have hpr : Kleiman.redAt k x x' (a ^ n) ≠ 0 := by rw [hp.2]; exact pow_ne_zero _ hr
    obtain ⟨-, h1, h2⟩ := Kleiman.locAt_inv hsp hp.1 hpr
    simp only [zpow_neg, zpow_natCast]
    rw [← hp.2]
    exact ⟨h1, h2⟩

end Loc

theorem GraphRestrict.full : GraphRestrict.Statement := by
  intro k _ N Ω _ _ x Q n m s K' _ _ x' s' hxy hgen hle ⟨i₀, hi₀⟩ ⟨j₁, hj₁⟩
  classical
  have hsp : Kleiman.primeOf (S := k) x ≤ Kleiman.primeOf (S := k) x' := by
    rw [← comap_mIdealOver_graph x s, ← comap_mIdealOver_graph x' s']
    exact Ideal.comap_mono hle
  obtain ⟨γ, hγ0, hg, hb⟩ := Kleiman.exists_restrict_gen hsp hxy Q

  have hmemQ : ∀ (I : Kleiman.Chart x') {i : Fin (N + 1)}, i ∈ I.1 → ∀ b,
      x i ^ (-n) * s b ∈ Q.sub (Kleiman.liftChart hxy I) := by
    intro I i hi b
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp ((Kleiman.liftChart hxy I).2.2 hi)
    have hsb : s b ∈ (Q.twist (Kleiman.twistSys k x n)).sub (Kleiman.liftChart hxy I) := by
      rw [← hgen]; exact Submodule.subset_span ⟨b, rfl⟩
    obtain ⟨q, hq, hqb⟩ :=
      (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n (Kleiman.liftChart hxy I) hi (s b)).mp hsb
    rw [hqb, smul_eq_mul, ← mul_assoc, ← zpow_add₀ hxi, neg_add_cancel, zpow_zero, one_mul]
    exact hq
  have hi₀I : i₀ ∈ (Kleiman.singleChart hi₀).1 := Finset.mem_singleton_self i₀
  have hx₀ : x i₀ ≠ 0 := hxy i₀ hi₀
  obtain ⟨t, ht⟩ : ∃ t : Fin m → Ω, t = fun b => x i₀ ^ (-n) * s b / γ := ⟨_, rfl⟩
  have htL : ∀ b, t b ∈ Kleiman.locAt k x x' := fun b => by
    rw [ht]; exact hg (Kleiman.singleChart hi₀) _ (hmemQ _ hi₀I b)

  obtain ⟨l₀, hl₀⟩ : ∃ l, Kleiman.redAt k x x' (t l) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b₀, -, hb₀L, hb₀r, hb₀Q⟩ := hb (Kleiman.singleChart hi₀)
    have hmem : x i₀ ^ n • (b₀ * γ) ∈
        (Q.twist (Kleiman.twistSys k x n)).sub (Kleiman.liftChart hxy (Kleiman.singleChart hi₀)) :=
      (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n _ hi₀I _).mpr ⟨_, hb₀Q, rfl⟩
    rw [← hgen, Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨a, ha⟩ := hmem
    simp only [Subalgebra.smul_def, smul_eq_mul] at ha
    have haL : ∀ b, (a b : Ω) ∈ Kleiman.locAt k x x' := fun b =>
      (Kleiman.chartRing_sub_locAt hsp hxy _ (a b).2).1
    have hsum : b₀ = ∑ b, (a b : Ω) * t b := by
      have hxn : x i₀ ^ n ≠ 0 := zpow_ne_zero n hx₀
      have : ∑ b, (a b : Ω) * t b = x i₀ ^ (-n) / γ * ∑ b, (a b : Ω) * s b := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by rw [ht]; ring
      rw [this, ha, zpow_neg]
      field_simp
    have hL := Kleiman.locAt_sum hsp Finset.univ (fun b => (a b : Ω) * t b) fun b _ =>
      (Kleiman.locAt_mul hsp (haL b) (htL b)).1
    apply hb₀r
    rw [hsum, hL.2]
    exact Finset.sum_eq_zero fun b _ => by
      rw [(Kleiman.locAt_mul hsp (haL b) (htL b)).2, hcon b, mul_zero]

  have htl0 : t l₀ ≠ 0 := (Kleiman.locAt_inv hsp (htL l₀) hl₀).1
  have hsl0 : s l₀ ≠ 0 := fun h0 => htl0 (by rw [ht]; simp [h0])
  have hkey : ∀ b, s' b * Kleiman.redAt k x x' (t l₀) = s' l₀ * Kleiman.redAt k x x' (t b) := by
    intro b
    obtain ⟨hdL, hdr⟩ := Kleiman.locAt_div hsp (htL b) (htL l₀) hl₀
    obtain ⟨f, h, e, hf, hh, hhy, hfh⟩ := hdL
    have hhx := Kleiman.aeval_ne_zero_of_primeOf_le hsp hh hhy
    have hr2 : Kleiman.redAt k x x' (t b) / Kleiman.redAt k x x' (t l₀) = aeval x' f / aeval x' h := by
      rw [← hdr, hfh, Kleiman.redAt_eq hsp hf hh hhy]
    have hst : t b / t l₀ = s b / s l₀ := by
      rw [div_eq_div_iff htl0 hsl0, ht]; dsimp only; ring
    rw [hst, div_eq_div_iff hsl0 hhx] at hfh
    have hgr := graphEq_of_le hle hf hh b l₀ (by rw [hfh]; ring)
    rw [div_eq_div_iff hl₀ hhy] at hr2
    apply mul_right_cancel₀ hhy
    linear_combination Kleiman.redAt k x x' (t l₀) * hgr - s' l₀ * hr2
  have hlam : s' l₀ ≠ 0 := by
    intro h0
    apply hj₁
    have := hkey j₁
    rw [h0, zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_right hl₀
  obtain ⟨μ, hμdef⟩ : ∃ μ : K', μ = s' l₀ / (Kleiman.redAt k x x' (t l₀) * x' i₀ ^ n) := ⟨_, rfl⟩
  have hμ : μ ≠ 0 := by
    rw [hμdef]; exact div_ne_zero hlam (mul_ne_zero hl₀ (zpow_ne_zero n hi₀))

  let Q'' : Kleiman.LineBundle k x' :=
    Kleiman.LineBundle.mk
      (Kleiman.SubFamily.mk (Kleiman.redSys hxy Q.toSubSystem γ) (Kleiman.redSys_mem_iff hsp hxy hg))
      (fun I => by
        obtain ⟨S0, hS0⟩ := Q.fg (Kleiman.liftChart hxy I)
        change (Kleiman.redSys hxy Q.toSubSystem γ).sub I |>.FG
        rw [Kleiman.redSys_sub_eq_span hsp hxy hg I hS0]
        exact Submodule.fg_span (S0.finite_toSet.image _))
      (fun I => Kleiman.redSys_invertible hsp hxy hγ0 hg I (hb I))
  have hR'' : Kleiman.RestrictData Q.toSubSystem hxy Q''.toSubSystem
      (fun q => Kleiman.redAt k x x' (q / γ)) := Kleiman.restrictData_redSys hsp hxy hg Q'' rfl
  have hR' := restrictData_scale hR'' μ hμ
  refine ⟨scaleBundle Q'' μ hμ, fun q => μ * Kleiman.redAt k x x' (q / γ), hR', ?_⟩
  intro I
  obtain ⟨i, hi⟩ := I.2.1
  have hxi' : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
  have hxi : x i ≠ 0 := hxy i hxi'

  have hc : ∀ b, x i ^ (-n) * s b / γ ∈ Kleiman.locAt k x x' ∧
      Kleiman.redAt k x x' (x i ^ (-n) * s b / γ) = (x' i₀ / x' i) ^ n * Kleiman.redAt k x x' (t b) := by
    intro b
    obtain ⟨hr1, hr2⟩ := locAt_ratio hsp hxi' i₀
    have hr0 : Kleiman.redAt k x x' (x i₀ / x i) ≠ 0 := by rw [hr2]; exact div_ne_zero hi₀ hxi'
    obtain ⟨hz1, hz2⟩ := locAt_zpow hsp hr1 hr0 n
    have hxn : x i ^ n ≠ 0 := zpow_ne_zero n hxi
    have hxn₀ : x i₀ ^ n ≠ 0 := zpow_ne_zero n hx₀
    have heq : x i ^ (-n) * s b / γ = (x i₀ / x i) ^ n * t b := by
      rw [ht, div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [heq, ← hr2, ← hz2]
    exact Kleiman.locAt_mul hsp hz1 (htL b)

  have hval : ∀ b, s' b = x' i ^ n * (μ * Kleiman.redAt k x x' (x i ^ (-n) * s b / γ)) := by
    intro b
    have hk := hkey b
    have hxn : x' i ^ n ≠ 0 := zpow_ne_zero n hxi'
    have hxn₀ : x' i₀ ^ n ≠ 0 := zpow_ne_zero n hi₀
    rw [(hc b).2, hμdef, div_zpow]
    field_simp
    linear_combination hk
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, TranslateEq.mem_twist_twistSys_iff _ n I hi]
    exact ⟨_, hR'.mem I _ (hmemQ I hi b), by rw [smul_eq_mul]; exact hval b⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (TranslateEq.mem_twist_twistSys_iff _ n I hi z).mp hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_span_singleton_mul.mp hw
    obtain ⟨q, hq, rfl⟩ := (Kleiman.mem_redSys_iff hsp hxy hg I v).mp hv
    have hxq : x i ^ n • q ∈ (Q.twist (Kleiman.twistSys k x n)).sub (Kleiman.liftChart hxy I) :=
      (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n _ hi _).mpr ⟨q, hq, rfl⟩
    rw [← hgen, Submodule.mem_span_range_iff_exists_fun] at hxq
    obtain ⟨a, ha⟩ := hxq
    simp only [Subalgebra.smul_def, smul_eq_mul] at ha
    have haL : ∀ b, (a b : Ω) ∈ Kleiman.locAt k x x' ∧ Kleiman.redAt k x x' (a b) ∈ Kleiman.chartRing k x' I :=
      fun b => Kleiman.chartRing_sub_locAt hsp hxy I (a b).2
    have hqs : q / γ = ∑ b, (a b : Ω) * (x i ^ (-n) * s b / γ) := by
      have hxn : x i ^ n ≠ 0 := zpow_ne_zero n hxi
      have : ∑ b, (a b : Ω) * (x i ^ (-n) * s b / γ) = x i ^ (-n) / γ * ∑ b, (a b : Ω) * s b := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [this, ha, zpow_neg]
      field_simp
    have hsumL := Kleiman.locAt_sum hsp Finset.univ (fun b => (a b : Ω) * (x i ^ (-n) * s b / γ))
      fun b _ => (Kleiman.locAt_mul hsp (haL b).1 (hc b).1).1
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun b => ⟨Kleiman.redAt k x x' (a b), (haL b).2⟩, ?_⟩
    simp only [Subalgebra.smul_def, smul_eq_mul]
    rw [hqs, hsumL.2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(Kleiman.locAt_mul hsp (haL b).1 (hc b).1).2, hval b]
    ring

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
