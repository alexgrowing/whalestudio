import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMonomialShift
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace MonomialShift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem exists_chart {y : (Σ k, ι k) → Ω} {d : ℕ} (hY : IsArithVar (mCoordIdeal y) d) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  have hrel := hY.2.1.2.2
  refine ⟨fun k => (hrel k).choose, fun k h0 => (hrel k).choose_spec ?_⟩
  change _ ∈ RingHom.ker _
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem norm_prod_le {P : Ideal (MRing ι)} {A : HermLine ι} {a : K → ℕ} (hM : MonomialsBounded P A a)
    (c : ∀ k, ι k) (j n : ℕ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    ‖∏ k, z ⟨k, c k⟩ ^ (j * a k + n)‖ ≤ A.h z ^ j * (fsH ι).h z ^ n := by
  classical
  have e1 : ‖∏ k, z ⟨k, c k⟩ ^ (j * a k + n)‖ =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) ^ j * (∏ k, ‖z ⟨k, c k⟩‖) ^ n := by
    rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow]
    ring

  let μ : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k := by
    intro k
    simp [μ]
  have hmon : ∏ p, z p ^ μ p = ∏ k, z ⟨k, c k⟩ ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [μ, pow_ite]
  have hA : ∏ k, ‖z ⟨k, c k⟩‖ ^ a k ≤ A.h z := by
    have := hM z hz μ hμ
    rw [hmon, norm_prod] at this
    simpa [norm_pow] using this
  have hH : ∏ k, ‖z ⟨k, c k⟩‖ ≤ (fsH ι).h z := by
    have hfs : (fsH ι).h z = ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
      rw [fsH, GroundTheory.Heights₂.Heights.Inter.ofMetrics_fs_h]
      simp
    rw [hfs]
    refine Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ (c k))
  rw [e1]
  gcongr
  exact pow_nonneg (A.pos z hz.1).le _

theorem isSmoothHerm_zcomb_fsH {A : HermLine ι} (hA : IsSmoothHerm A) (q : ℕ) :
    IsSmoothHerm (HermLine.zcomb A (fsH ι) q 1) := by
  have hH : IsSmoothHerm (fsH ι) := GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have hfun : (HermLine.zcomb A (fsH ι) q 1).h = fun z => A.h z ^ q * (fsH ι).h z := by
    funext z
    change A.h z ^ ((q : ℕ) : ℤ) * (fsH ι).h z ^ (1 : ℤ) = _
    rw [zpow_natCast, zpow_one]
  unfold IsSmoothHerm at hA hH ⊢
  rw [hfun]
  exact (hA.pow q).mul hH

theorem proof (hPack : PackingStatement) : MonomialShift.Statement := by
  intro K _ ι _ Ω _ y D a A P0 q τ n hY hBir ha hP0 hsemi hM hq hτ
  classical
  obtain ⟨c, hc⟩ := exists_chart hY

  obtain ⟨e, he⟩ : ∃ e : K → ℕ, e = fun k => (q * n - τ) * a k + n := ⟨_, rfl⟩
  have hBa : ∀ k, (HermLine.zcomb A (fsH ι) q 1).a k = (q : ℤ) * a k + 1 := by
    intro k
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics, ha]
  have hdeg : ∀ k, (n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k = τ * A.a k + e k := by
    intro k
    rw [hBa, he]
    simp only [ha]
    push_cast [Nat.cast_sub hτ]
    ring

  obtain ⟨mv, hmv⟩ : ∃ mv : Ω, mv = ∏ k, y ⟨k, c k⟩ ^ e k := ⟨_, rfl⟩
  have hmv0 : mv ≠ 0 := by
    rw [hmv]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hmvx : aeval y (xpow c e) = mv := by
    simp [hmv, xpow]

  have hlat : ∀ s ∈ chartLatNm y A.a τ, mv * s ∈ chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n := by
    intro s hs c' hc'
    have h1 := hs c' hc'
    have h2 : ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k ∈ integralClosure (chartRingZ y c') Ω := by
      have hmem : ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k ∈ chartRingZ y c' :=
        Subalgebra.prod_mem _ fun k _ =>
          pow_mem (Algebra.subset_adjoin
            (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c' p.1⟩) ⟨k, c k⟩)) _
      exact (integralClosure (chartRingZ y c') Ω).algebraMap_mem ⟨_, hmem⟩
    have hsplit : ∀ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k)) =
        y ⟨k, c' k⟩ ^ (-((τ : ℤ) * A.a k)) * (y ⟨k, c' k⟩ ^ e k)⁻¹ := by
      intro k
      rw [hdeg k, neg_add, zpow_add₀ (hc' k), zpow_neg (y _) ((e k : ℕ) : ℤ), zpow_natCast]
    have key : mv * s * ∏ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k)) =
        (s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * A.a k))) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k := by
      simp only [hsplit, div_eq_mul_inv, mul_pow, inv_pow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hmv]
      ring
    rw [key]
    exact mul_mem h1 h2

  have hsmall : ∀ s, IsSmallH (mCoordIdeal y) y A τ s →
      IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (mv * s) := by
    intro s hs dg dh g h z hg hh hd hgh hz
    have hmh := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (isMultiHomog_xpow c e) hh
    have hb := hs dg (e + dh) g (xpow c e * h) z hg hmh
      (fun k => by have := hd k; have := hdeg k; simp only [Pi.add_apply]; push_cast; linarith)
      (by rw [hgh, map_mul, hmvx]; ring) hz
    have hApos : 0 < A.h z := A.pos z hz.1
    have hxz : eval z (map (Int.castRingHom ℂ) (xpow c e)) = ∏ k, z ⟨k, c k⟩ ^ ((q * n - τ) * a k + n) := by
      simp [xpow, he]
    have hBh : (HermLine.zcomb A (fsH ι) q 1).h z = A.h z ^ ((q : ℕ) : ℤ) * (fsH ι).h z ^ (1 : ℤ) := rfl
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖
        ≤ ‖eval z (map (Int.castRingHom ℂ) (xpow c e * h))‖ * A.h z ^ τ := hb
      _ = ‖∏ k, z ⟨k, c k⟩ ^ ((q * n - τ) * a k + n)‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
          rw [map_mul, eval_mul, norm_mul, hxz]
      _ ≤ (A.h z ^ (q * n - τ) * (fsH ι).h z ^ n) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
          gcongr
          exact norm_prod_le hM c (q * n - τ) n hz
      _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (HermLine.zcomb A (fsH ι) q 1).h z ^ n := by
          rw [hBh, zpow_natCast, zpow_one, mul_pow, ← pow_mul,
            show A.h z ^ (q * n) = A.h z ^ (q * n - τ) * A.h z ^ τ by rw [← pow_add, Nat.sub_add_cancel hτ]]
          ring

  let f : {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} →
      {t : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n //
        IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (t : Ω)} :=
    fun s => ⟨⟨mv * s.1, hlat s.1 s.1.2⟩, hsmall s.1 s.2⟩
  have hinj : Function.Injective f := by
    intro s t hst
    have h := congrArg (fun u => ((u.1 : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n) : Ω)) hst
    exact Subtype.ext (Subtype.ext (mul_left_cancel₀ hmv0 h))
  have hfin := (hPack K ι Ω y D (HermLine.zcomb A (fsH ι) q 1)
    (chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a) hY hBir (isSmoothHerm_zcomb_fsH hsemi.1 q)
    (fun _ => le_rfl)).1 n
  have : Finite {t : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (t : Ω)} := hfin.to_subtype
  have hcard := Nat.card_le_card_of_injective f hinj
  unfold smallSectionCount
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)})
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end MonomialShift

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
