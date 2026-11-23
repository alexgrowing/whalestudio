import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagPull
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.sq_diag

theorem isMultiHomog_X_pow' {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (k : K') (i : ι' k) (n : ℕ) :
    IsMultiHomog ((X ⟨k, i⟩ : MRing ι') ^ n) (Pi.single k n) := by
  classical
  rw [X_pow_eq_monomial]
  intro m hm l
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  by_cases hl : l = k
  · subst hl
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · simp
  · rw [Pi.single_eq_of_ne hl]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hl (Sigma.mk.inj_iff.mp h).1.symm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ} {k₀ : K}
  {xi2 : K → ℤ} (Q : AlgSq P d k₀ xi2)

theorem block_surj (j : Fin 2) (k : K) (a : Q.ιW (Q.κ j k)) : ∃ i : ι k, Q.v j ⟨k, i⟩ = ⟨Q.κ j k, a⟩ := by
  obtain ⟨p, hp⟩ := (Q.block j).2.2.2 ⟨Q.κ j k, a⟩ ⟨k, rfl⟩
  have h1 : Q.κ j p.1 = Q.κ j k := by rw [← (Q.block j).2.2.1 p, hp]
  have h2 := (Q.block j).1 h1
  obtain ⟨k', i⟩ := p
  simp only at h2
  subst h2
  exact ⟨i, hp⟩

theorem exists_notMem (j : Fin 2) {W : Ideal (MRing Q.ιW)} (hr : IsRelevant W) :
    ∃ i : ι k₀, (X (Q.v j ⟨k₀, i⟩) : MRing Q.ιW) ∉ W := by
  obtain ⟨a, ha⟩ := hr (Q.κ j k₀)
  obtain ⟨i, hi⟩ := block_surj Q j k₀ a
  exact ⟨i, by rw [hi]; exact ha⟩

theorem exists_both {W : Ideal (MRing Q.ιW)} (hW : W.IsPrime) (hΔW : Q.Δ ≤ W) (hr : IsRelevant W) :
    ∃ i : ι k₀, (X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) ∉ W ∧ (X (Q.v 1 ⟨k₀, i⟩) : MRing Q.ιW) ∉ W := by
  obtain ⟨i, hi⟩ := exists_notMem Q 0 hr
  obtain ⟨i', hi'⟩ := exists_notMem Q 1 hr
  have hd := hΔW (Q.diag i i')
  have hprod : (X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) * X (Q.v 1 ⟨k₀, i'⟩) ∉ W :=
    fun h => (hW.mem_or_mem h).elim hi hi'
  have h2 : (X (Q.v 0 ⟨k₀, i'⟩) : MRing Q.ιW) * X (Q.v 1 ⟨k₀, i⟩) ∉ W := fun h => hprod (by
    have := W.add_mem hd h
    simpa using this)
  exact ⟨i', fun h => h2 (W.mul_mem_right _ h), hi'⟩

theorem cross (n : ℕ) (i j : ι k₀) :
    (X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) ^ n * X (Q.v 1 ⟨k₀, j⟩) ^ n -
      (X (Q.v 1 ⟨k₀, i⟩) : MRing Q.ιW) ^ n * X (Q.v 0 ⟨k₀, j⟩) ^ n ∈ Q.Δ := by
  have h := Q.diag i j
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow ((X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) * X (Q.v 1 ⟨k₀, j⟩))
    (X (Q.v 0 ⟨k₀, j⟩) * X (Q.v 1 ⟨k₀, i⟩)) n
  have e : (X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) ^ n * X (Q.v 1 ⟨k₀, j⟩) ^ n -
      (X (Q.v 1 ⟨k₀, i⟩) : MRing Q.ιW) ^ n * X (Q.v 0 ⟨k₀, j⟩) ^ n =
      (X (Q.v 0 ⟨k₀, i⟩) * X (Q.v 1 ⟨k₀, j⟩)) ^ n - (X (Q.v 0 ⟨k₀, j⟩) * X (Q.v 1 ⟨k₀, i⟩)) ^ n := by ring
  rw [e, hc]
  exact Q.Δ.mul_mem_right _ h

theorem multAt_eq_locLen' {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (J W : Ideal (MRing ι')) (hW : W.IsPrime) :
    multAt J W = (locLen (MRing ι' ⧸ J) ⟨W, hW⟩).toNat := by
  simp [multAt, hW, locLen]

theorem divCycle_eq (n : ℕ) (i : ι k₀) :
    divCycle Q.Δ ((X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) ^ n) = divCycle Q.Δ ((X (Q.v 1 ⟨k₀, i⟩) : MRing Q.ιW) ^ n) := by
  classical
  have hV : Q.Δ.IsPrime := Q.arithΔ.2.1.1
  have hc : ∀ j : ι k₀, (X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) ^ n * X (Q.v 1 ⟨k₀, j⟩) ^ n -
      (X (Q.v 1 ⟨k₀, i⟩) : MRing Q.ιW) ^ n * X (Q.v 0 ⟨k₀, j⟩) ^ n ∈ Q.Δ := fun j => cross Q n i j
  have hc' : ∀ j : ι k₀, (X (Q.v 1 ⟨k₀, i⟩) : MRing Q.ιW) ^ n * X (Q.v 0 ⟨k₀, j⟩) ^ n -
      (X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) ^ n * X (Q.v 1 ⟨k₀, j⟩) ^ n ∈ Q.Δ := fun j => by
    rw [← neg_sub]
    exact neg_mem (hc j)
  have hsupp : ∀ W, W ∈ divSupp Q.Δ ((X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) ^ n) ↔
      W ∈ divSupp Q.Δ ((X (Q.v 1 ⟨k₀, i⟩) : MRing Q.ιW) ^ n) := by
    intro W
    constructor
    · rintro ⟨hW, hr⟩
      obtain ⟨j, h0, h1⟩ := exists_both Q hW.1.1 (le_sup_left.trans hW.1.2) hr
      exact ⟨GroundTheory.Heights₂.Heights.Inter.DiagPull.mem_minimalPrimes_of_cross (hc j) hW
        (fun h => h0 (hW.1.1.mem_of_pow_mem _ h)) (fun h => h1 (hW.1.1.mem_of_pow_mem _ h)), hr⟩
    · rintro ⟨hW, hr⟩
      obtain ⟨j, h0, h1⟩ := exists_both Q hW.1.1 (le_sup_left.trans hW.1.2) hr
      exact ⟨GroundTheory.Heights₂.Heights.Inter.DiagPull.mem_minimalPrimes_of_cross (hc' j) hW
        (fun h => h1 (hW.1.1.mem_of_pow_mem _ h)) (fun h => h0 (hW.1.1.mem_of_pow_mem _ h)), hr⟩
  ext W
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  by_cases h : W ∈ divSupp Q.Δ ((X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) ^ n)
  · rw [if_pos h, if_pos ((hsupp W).1 h)]
    obtain ⟨hW, hr⟩ := h
    have hWp := hW.1.1
    obtain ⟨j, h0, h1⟩ := exists_both Q hWp (le_sup_left.trans hW.1.2) hr
    rw [multAt_eq_locLen' _ _ hWp, multAt_eq_locLen' _ _ hWp,
      GroundTheory.Heights₂.Heights.Inter.DiagPull.locLen_cross hV (hc j) ⟨W, hWp⟩ (le_sup_left.trans hW.1.2)
        (fun h => h0 (hWp.mem_of_pow_mem _ h)) (fun h => h1 (hWp.mem_of_pow_mem _ h))]
  · rw [if_neg h, if_neg (mt (hsupp W).2 h)]

theorem exists_prop {z : (Σ k, Q.ιW k) → ℂ} (hz : z ∈ mcPts Q.Δ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ i : ι k₀, z (Q.v 1 ⟨k₀, i⟩) = c * z (Q.v 0 ⟨k₀, i⟩) := by
  have hmin : ∀ i k : ι k₀, z (Q.v 0 ⟨k₀, i⟩) * z (Q.v 1 ⟨k₀, k⟩) - z (Q.v 0 ⟨k₀, k⟩) * z (Q.v 1 ⟨k₀, i⟩) = 0 := by
    intro i k
    have := hz.2 _ (Q.diag i k)
    simpa using this
  obtain ⟨a, ha⟩ := hz.1 (Q.κ 0 k₀)
  obtain ⟨i, hi⟩ := block_surj Q 0 k₀ a
  obtain ⟨b, hb⟩ := hz.1 (Q.κ 1 k₀)
  obtain ⟨j, hj⟩ := block_surj Q 1 k₀ b
  have hi' : z (Q.v 0 ⟨k₀, i⟩) ≠ 0 := by rw [hi]; exact ha
  have hj' : z (Q.v 1 ⟨k₀, j⟩) ≠ 0 := by rw [hj]; exact hb
  have hk : ∀ k : ι k₀, z (Q.v 1 ⟨k₀, k⟩) = z (Q.v 1 ⟨k₀, i⟩) / z (Q.v 0 ⟨k₀, i⟩) * z (Q.v 0 ⟨k₀, k⟩) := by
    intro k
    have h := hmin i k
    field_simp
    linear_combination h
  refine ⟨z (Q.v 1 ⟨k₀, i⟩) / z (Q.v 0 ⟨k₀, i⟩), fun h0 => hj' ?_, hk⟩
  rw [hk j, h0, zero_mul]

theorem nonempty_ι (Q : AlgSq P d k₀ xi2) (k : K) : Nonempty (ι k) := by
  obtain ⟨a, _⟩ := Q.arithW.2.1.2.2 (Q.κ 0 k)
  obtain ⟨i, _⟩ := block_surj Q 0 k a
  exact ⟨i⟩

theorem κ_eq (k : K) (hk : k ≠ k₀) : Q.κ 0 k = Q.κ 1 k := by
  obtain ⟨i⟩ := nonempty_ι Q k
  rw [← (Q.block 0).2.2.1 ⟨k, i⟩, ← (Q.block 1).2.2.1 ⟨k, i⟩, Q.same ⟨k, i⟩ hk]

theorem κ_ne : Q.κ 0 k₀ ≠ Q.κ 1 k₀ := fun h => Q.new ⟨k₀, h⟩

open Classical in
theorem pull_norm (A : HermLine ι) {z : (Σ k, Q.ιW k) → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hk : ∀ i : ι k₀, z (Q.v 1 ⟨k₀, i⟩) = c * z (Q.v 0 ⟨k₀, i⟩)) :
    A.h (fun p => z (Q.v 1 p)) = ‖c‖ ^ (A.a k₀) * A.h (fun p => z (Q.v 0 p)) := by
  have e : (fun p => z (Q.v 1 p)) = fun p : (Σ k, ι k) => (if p.1 = k₀ then c else 1) * z (Q.v 0 p) := by
    funext p
    obtain ⟨k, i⟩ := p
    by_cases h : k = k₀
    · subst h
      simp [hk i]
    · simp [h, Q.same ⟨k, i⟩ h]
  rw [e]
  refine (A.smul (fun k => if k = k₀ then c else 1) (fun p => z (Q.v 0 p)) (fun k => by split_ifs <;> simp [hc])).trans ?_
  congr 1
  rw [Finset.prod_eq_single k₀]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

open Classical in
theorem key (n : ℕ) (i : ι k₀) (hi0 : (X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) ∉ Q.Δ)
    (hi1 : (X (Q.v 1 ⟨k₀, i⟩) : MRing Q.ιW) ∉ Q.Δ) (B₀ B₁ : HermLine Q.ιW)
    (hdeg : ∀ k, B₀.a k - B₁.a k = (if k = Q.κ 0 k₀ then (n : ℤ) else 0) - (if k = Q.κ 1 k₀ then (n : ℤ) else 0))
    (hnorm : ∀ z ∈ mcPts Q.Δ, ‖z (Q.v 0 ⟨k₀, i⟩)‖ ^ n * B₁.h z = ‖z (Q.v 1 ⟨k₀, i⟩)‖ ^ n * B₀.h z) :
    VertClose Q.Δ ∅ (fun _ => 0) B₀ B₁ := by
  classical
  have hV : Q.Δ.IsPrime := Q.arithΔ.2.1.1
  have h0 : IsMultiHomog ((X (Q.v 0 ⟨k₀, i⟩) : MRing Q.ιW) ^ n) (Pi.single (Q.κ 0 k₀) n) := by
    have := isMultiHomog_X_pow' (ι' := Q.ιW) (Q.v 0 ⟨k₀, i⟩).1 (Q.v 0 ⟨k₀, i⟩).2 n
    rw [Sigma.eta, (Q.block 0).2.2.1] at this
    exact this
  have h1 : IsMultiHomog ((X (Q.v 1 ⟨k₀, i⟩) : MRing Q.ιW) ^ n) (Pi.single (Q.κ 1 k₀) n) := by
    have := isMultiHomog_X_pow' (ι' := Q.ιW) (Q.v 1 ⟨k₀, i⟩).1 (Q.v 1 ⟨k₀, i⟩).2 n
    rw [Sigma.eta, (Q.block 1).2.2.1] at this
    exact this
  refine ⟨_, _, _, _, h0, h1, fun h => hi0 (hV.mem_of_pow_mem _ h), fun h => hi1 (hV.mem_of_pow_mem _ h),
    fun k => ?_, fun z hz => ?_, fun W _ => by rw [divCycle_eq Q n i], fun W h => by simp at h⟩
  · rw [hdeg k]
    by_cases ha : k = Q.κ 0 k₀
    · subst ha
      have hb : ¬ Q.κ 0 k₀ = Q.κ 1 k₀ := κ_ne Q
      simp [Pi.single_apply, hb]
    · by_cases hb : k = Q.κ 1 k₀
      · subst hb
        simp [Pi.single_apply, ha]
      · simp [Pi.single_apply, ha, hb]
  · simp only [map_pow, map_X, eval_X, norm_pow]
    exact hnorm z hz

end PositivityTheory.Xgp.sq_diag

theorem PositivityTheory.Xgp.t_sq_diag : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (A : HermLine ι) (A₀ A₁ : HermLine Q.ιW), IsPullHerm (Q.κ 0) (Q.v 0) A A₀ → IsPullHerm (Q.κ 1) (Q.v 1) A A₁ → VertClose Q.Δ ∅ (fun _ => 0) A₀ A₁ := by
  intro K _ ι _ P d k₀ xi2 Q A A₀ A₁ h0 h1
  classical
  have hΔ : Q.Δ.IsPrime := Q.arithΔ.2.1.1
  obtain ⟨i, hi0, hi1⟩ := PositivityTheory.Xgp.sq_diag.exists_both Q hΔ le_rfl Q.arithΔ.2.1.2.2
  have ha0 : ∀ k, A₀.a k = Function.extend (Q.κ 0) A.a 0 k := fun k => congrFun h0.1 k
  have ha1 : ∀ k, A₁.a k = Function.extend (Q.κ 1) A.a 0 k := fun k => congrFun h1.1 k
  have hinj0 := (Q.block 0).1
  have hinj1 := (Q.block 1).1
  have hne := PositivityTheory.Xgp.sq_diag.κ_ne Q

  have hdeg : ∀ k, A₀.a k - A₁.a k =
      (if k = Q.κ 0 k₀ then A.a k₀ else 0) - (if k = Q.κ 1 k₀ then A.a k₀ else 0) := by
    intro k
    rw [ha0, ha1]
    by_cases hk0 : k = Q.κ 0 k₀
    · subst hk0
      rw [hinj0.extend_apply, Function.extend_apply', if_pos rfl, if_neg hne]
      · simp
      · rintro ⟨a, ha⟩
        by_cases hak : a = k₀
        · subst hak
          exact hne ha.symm
        · rw [← PositivityTheory.Xgp.sq_diag.κ_eq Q a hak] at ha
          exact hak (hinj0 ha)
    · by_cases hk1 : k = Q.κ 1 k₀
      · subst hk1
        rw [hinj1.extend_apply, Function.extend_apply', if_neg hk0, if_pos rfl]
        · simp
        · rintro ⟨a, ha⟩
          exact Q.new ⟨a, ha⟩
      · rw [if_neg hk0, if_neg hk1]
        rcases Q.all k with ⟨a, rfl⟩ | h
        · have hak : a ≠ k₀ := fun h => hk0 (by rw [h])
          rw [hinj0.extend_apply, PositivityTheory.Xgp.sq_diag.κ_eq Q a hak, hinj1.extend_apply]
          simp
        · exact absurd h hk1

  have hnorm : ∀ z ∈ mcPts Q.Δ, ∃ c : ℂ, c ≠ 0 ∧ z (Q.v 1 ⟨k₀, i⟩) = c * z (Q.v 0 ⟨k₀, i⟩) ∧
      A₁.h z = ‖c‖ ^ (A.a k₀) * A₀.h z := by
    intro z hz
    obtain ⟨c, hc, hk⟩ := PositivityTheory.Xgp.sq_diag.exists_prop Q hz
    refine ⟨c, hc, hk i, ?_⟩
    rw [h0.2, h1.2]
    exact PositivityTheory.Xgp.sq_diag.pull_norm Q A hc hk
  rcases le_or_gt 0 (A.a k₀) with hm | hm
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hm
    refine PositivityTheory.Xgp.sq_diag.key Q n i hi0 hi1 A₀ A₁ (fun k => by rw [hdeg k, hn] <;> split_ifs <;> simp) fun z hz => ?_
    obtain ⟨c, hc, hzc, hh⟩ := hnorm z hz
    rw [hh, hzc, hn, zpow_natCast, norm_mul, mul_pow]
    ring
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hm.le
    refine (PositivityTheory.Xgp.sq_diag.key Q n i hi0 hi1 A₁ A₀ (fun k => ?_) fun z hz => ?_).symm
    · rw [show A₁.a k - A₀.a k = -(A₀.a k - A₁.a k) by ring, hdeg k, hn]
      split_ifs <;> ring
    · obtain ⟨c, hc, hzc, hh⟩ := hnorm z hz
      rw [hh, hzc, hn, zpow_neg, zpow_natCast, norm_mul, mul_pow]
      have hc' : ‖c‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
      field_simp
