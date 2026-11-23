import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.XMulMemSpanOfColemanLevelsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorIterateSuccCongrFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvNormOpEqNrmStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsColemanLevelRingBasisOneAddXPowStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsAdicCompleteComapConstantCoeff

open GlobalTheory.Col PowerSeries

namespace GlobalTheory.ColEx

theorem iter_cong : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ h : PowerSeries R, IsUnit h → ∀ j i : ℕ, ∃ r : PowerSeries R, (normOp p)^[j + i] h = (smap σ)^[i] ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  intro R _ p _ σ hF h hh j i
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := GlobalTheory.T.colemanNormOperator_iterate_succ_congr_frobenius R p σ hF h hh (j + i)
    refine ⟨smap σ r + (p : PowerSeries R) ^ i * r', ?_⟩
    rw [show j + (i + 1) = (j + i) + 1 by omega, hr', hr, Function.iterate_succ_apply' (smap σ), map_add, map_mul, map_pow, map_natCast]
    ring

theorem norm_tower : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R → ∀ u : ∀ m : ℕ, (lev R p (m + 1))ˣ, (∀ m : ℕ, nrm p (m + 1) (by omega) ((u (m + 1) : lev R p (m + 2))) = (u m : lev R p (m + 1))) → ∀ (m i : ℕ) (h : PowerSeries R), ev R p (m + i + 1) h = (u (m + i) : lev R p (m + i + 1)) → ev R p (m + 1) ((normOp p)^[i] h) = u m := by
  intro R _ p _ hR u hu m i
  induction i with
  | zero => intro h hh; exact hh
  | succ i ih =>
    intro h hh
    rw [Function.iterate_succ_apply]
    apply ih
    rw [GlobalTheory.T.ev_normOp_eq_nrm_ev_succ R p (m + i + 1) (by omega) hR h, ← hu (m + i)]
    congr 1

theorem ev_map_congr : ∀ (R : Type) [CommRing R] (p m : ℕ) (τ : R →+* R) (g g' : PowerSeries R), ev R p m g = ev R p m g' → ev R p m (PowerSeries.map τ g) = ev R p m (PowerSeries.map τ g') := by
  intro R _ p m τ g g' hg
  have hc : PowerSeries.map τ (cyc R p m) = cyc R p m := by
    unfold cyc
    rw [Polynomial.hom_eval₂]
    have h1 : (PowerSeries.map τ).comp (PowerSeries.C (R := R)) = (PowerSeries.C (R := R)).comp τ := by
      ext a : 1; simp
    rw [h1, map_add, map_one, PowerSeries.map_X, ← Polynomial.eval₂_map, Polynomial.map_cyclotomic]
  rw [Ideal.Quotient.eq] at hg ⊢
  rw [← map_sub]
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 hg
  rw [← hc', map_mul, hc]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

end GlobalTheory.ColEx

namespace GlobalTheory.ColEx

theorem unit_of_ev : ∀ (R : Type) [CommRing R] (p n : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R → ∀ g : PowerSeries R, IsUnit (ev R p n g) → IsUnit g := by
  intro R _ p n hp hR g hg
  haveI := hR
  obtain ⟨w, hw⟩ := hg.exists_right_inv
  obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [← map_mul, ← map_one (ev R p n), Ideal.Quotient.eq] at hw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hw
  have hcyc : constantCoeff (cyc R p n) ∈ Ideal.span {(p : R)} := by
    have e : constantCoeff (cyc R p n) = (Polynomial.cyclotomic (p ^ n) R).eval 1 := by
      unfold cyc
      rw [Polynomial.hom_eval₂]
      have h1 : (constantCoeff (R := R)).comp (PowerSeries.C (R := R)) = RingHom.id R := by ext a; simp
      rw [h1, map_add, map_one, constantCoeff_X, add_zero]
      rfl
    rw [e]
    rcases n with _ | n
    · simp
    · rw [Polynomial.eval_one_cyclotomic_prime_pow]; exact Ideal.subset_span rfl
  have hj : constantCoeff g * constantCoeff g' - 1 ∈ Ideal.jacobson (⊥ : Ideal R) := by
    have := congrArg (constantCoeff (R := R)) hc
    rw [map_mul, map_sub, map_mul, map_one] at this
    rw [← this]
    exact IsAdicComplete.le_jacobson_bot _ (Ideal.mul_mem_left _ _ hcyc)
  have hu : IsUnit (constantCoeff g * constantCoeff g') := by
    have := (Ideal.mem_jacobson_bot.1 hj) 1
    simpa using this
  exact PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_of_mul_isUnit_left hu)

theorem one_add_X_pow_sub_one_mem : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] (j : ℕ), (1 + X : PowerSeries R) ^ (p ^ j) - 1 ∈ ((Ideal.span {(p : R)}).comap (constantCoeff (R := R))) ^ (j + 1) := by
  intro R _ p hp j
  have hpJ : (p : PowerSeries R) ∈ (Ideal.span {(p : R)}).comap (constantCoeff (R := R)) := by
    rw [Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl
  have hXJ : (X : PowerSeries R) ∈ (Ideal.span {(p : R)}).comap (constantCoeff (R := R)) := by
    rw [Ideal.mem_comap, constantCoeff_X]; exact Ideal.zero_mem _
  induction j with
  | zero => simpa using hXJ
  | succ j ih =>
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out ((1 + X : PowerSeries R) ^ (p ^ j) - 1) 1
    have e : (1 + X : PowerSeries R) ^ (p ^ (j + 1)) - 1 = ((1 + X : PowerSeries R) ^ (p ^ j) - 1) ^ p
        + (p : PowerSeries R) * ((1 + X : PowerSeries R) ^ (p ^ j) - 1) * 1 * r := by
      rw [sub_add_cancel, one_pow, ← pow_mul, ← pow_succ] at hr
      rw [hr]; ring
    rw [e]
    refine Ideal.add_mem _ ?_ ?_
    · have := Ideal.pow_mem_pow ih p
      rw [← pow_mul] at this
      exact Ideal.pow_le_pow_right (by nlinarith [hp.out.two_le]) this
    · rw [mul_one, pow_succ']
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hpJ ih)

theorem ev_of_mem_pow : ∀ (R : Type) [CommRing R] (p m N : ℕ) [Fact p.Prime] (g : PowerSeries R), g ∈ ((Ideal.span {(p : R)}).comap (constantCoeff (R := R))) ^ (p ^ m * N) → ∃ y : PowerSeries R, ev R p m g = ev R p m ((p : PowerSeries R) ^ N * y) := by
  intro R _ p m N hp g hg
  have hXp : ev R p m X ^ (p ^ m) ∈ Ideal.span {(p : lev R p m)} := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out (X : PowerSeries R) 1 m
    obtain ⟨s, hs⟩ := cyc_dvd_level (R := R) p m
    have h0 : ev R p m ((1 + X : PowerSeries R) ^ (p ^ m) - 1) = 0 := by
      rw [hs, map_mul, ev_cyc_self, zero_mul]
    rw [add_comm (1 : PowerSeries R) X, hr] at h0
    simp only [map_sub, map_add, map_mul, map_pow, map_one, one_pow, map_natCast] at h0
    rw [Ideal.mem_span_singleton']
    exact ⟨-(ev R p m X * ev R p m r), by linear_combination -h0⟩
  have hJP : ((Ideal.span {(p : R)}).comap (constantCoeff (R := R))) ^ (p ^ m)
      ≤ Ideal.comap (ev R p m) (Ideal.span {(p : lev R p m)}) := by
    intro g hg
    rw [GlobalTheory.ChartRing.mem_pow_comap_constantCoeff_iff] at hg
    rw [g.eq_X_pow_mul_shift_add_trunc (p ^ m)]
    refine Ideal.add_mem _ ?_ ?_
    · rw [Ideal.mem_comap, map_mul, map_pow]; exact Ideal.mul_mem_right _ _ hXp
    · rw [trunc_apply, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
      refine Ideal.sum_mem _ fun i hi => ?_
      have hi' : i < p ^ m := (Finset.mem_Ico.1 hi).2
      rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial, monomial_eq_C_mul_X_pow]
      have hc : coeff i g ∈ Ideal.span {(p : R)} := Ideal.pow_le_self (by omega) (hg i)
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hc
      have e : (C (coeff i g) * X ^ i : PowerSeries R) = (p : PowerSeries R) * (C d * X ^ i) := by
        rw [← hd, map_mul, map_natCast]; ring
      rw [e, Ideal.mem_comap, map_mul, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have h2 : g ∈ (Ideal.comap (ev R p m) (Ideal.span {(p : lev R p m)})) ^ N := by
    rw [pow_mul] at hg
    exact Ideal.pow_right_mono hJP N hg
  have h3 := Ideal.le_comap_pow (f := ev R p m) (K := Ideal.span {(p : lev R p m)}) N h2
  rw [Ideal.mem_comap, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h3
  obtain ⟨z, hz⟩ := h3
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨y, by rw [← hz, map_mul, map_pow, map_natCast, mul_comm]⟩

theorem lev_sep : ∀ (R : Type) [CommRing R] (p m : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R → ∀ x : lev R p m, (∀ N : ℕ, ∃ y : PowerSeries R, x = ev R p m ((p : PowerSeries R) ^ N * y)) → x = 0 := by
  intro R _ p m _ hR x hx
  haveI := hR
  obtain ⟨b, -⟩ := GlobalTheory.T.exists_colemanLevelRing_basis_one_add_X_pow R p m hR
  apply b.repr.injective
  rw [map_zero]
  ext i
  rw [Finsupp.coe_zero, Pi.zero_apply]
  apply IsHausdorff.haus' (I := Ideal.span {(p : R)}) (b.repr x i)
  intro N
  obtain ⟨y, hy⟩ := hx N
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have e : x = ((p : R) ^ N) • ev R p m y := by
    rw [hy, Algebra.smul_def, map_mul, map_pow, map_pow, map_natCast, map_natCast]
  rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

end GlobalTheory.ColEx

namespace GlobalTheory.Col

theorem exists_coleman_series : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ u : ∀ m : ℕ, (lev R p (m + 1))ˣ, (∀ m : ℕ, nrm p (m + 1) (by omega) ((u (m + 1) : lev R p (m + 2))) = (u m : lev R p (m + 1))) → ∃ f : (PowerSeries R)ˣ, ∀ m : ℕ, ev R p (m + 1) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) (f : PowerSeries R)) = u m := by
  intro R _ p hp σ hF u hu
  have hR := hF.complete
  haveI : IsAdicComplete (Ideal.span {(p : R)}) R := hF.complete
  haveI : IsAdicComplete ((Ideal.span {(p : R)}).comap (constantCoeff (R := R))) (PowerSeries R) :=
    GlobalTheory.ChartRing.isAdicComplete_comap_constantCoeff _
  set J : Ideal (PowerSeries R) := (Ideal.span {(p : R)}).comap (constantCoeff (R := R)) with hJ

  have hcoeff : ∀ (k : ℕ) (x : PowerSeries R) (n : ℕ), coeff n ((smap σ)^[k] x) = (⇑σ)^[k] (coeff n x) := by
    intro k
    induction k with
    | zero => intro x n; rfl
    | succ k ih =>
      intro x n
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coeff_map, ih]
      rfl
  have hτ' : ∀ (m : ℕ) (x : PowerSeries R) (n : ℕ),
      coeff n (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) x) = (⇑σ.symm)^[m + 1] (coeff n x) := by
    intro m x n; rw [coeff_map, RingHom.coe_pow]; rfl
  have hτ : ∀ (m : ℕ) (x : PowerSeries R) (n : ℕ),
      coeff n (PowerSeries.map (((σ : R ≃+* R) : R →+* R) ^ (m + 1)) x) = (⇑σ)^[m + 1] (coeff n x) := by
    intro m x n; rw [coeff_map, RingHom.coe_pow]; rfl
  have hcancel : ∀ (m a : ℕ) (x : PowerSeries R), m + 1 ≤ a →
      PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) ((smap σ)^[a] x) = (smap σ)^[a - (m + 1)] x := by
    intro m a x h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    ext n
    rw [hτ', hcoeff, hcoeff, Function.iterate_add_apply (⇑σ) (m + 1) d, Nat.add_sub_cancel_left]
    exact (Function.LeftInverse.iterate (fun c => σ.symm_apply_apply c) (m + 1)) _
  have hinv : ∀ (m : ℕ) (x : PowerSeries R), PowerSeries.map (((σ : R ≃+* R) : R →+* R) ^ (m + 1))
      (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) x) = x := by
    intro m x
    ext n
    rw [hτ, hτ']
    exact (Function.LeftInverse.iterate (fun c => σ.apply_symm_apply c) (m + 1)) _

  have hmapJ : ∀ (τ : R →+* R) (n : ℕ) (g : PowerSeries R), g ∈ J ^ n → PowerSeries.map τ g ∈ J ^ n := by
    intro τ n g hg
    rw [hJ, GlobalTheory.ChartRing.mem_pow_comap_constantCoeff_iff] at hg ⊢
    intro i
    have := hg i
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at this ⊢
    obtain ⟨c, hc⟩ := this
    exact ⟨τ c, by rw [coeff_map, ← hc, map_mul, map_pow, map_natCast]⟩

  have hdivX : ∀ (n : ℕ) (g : PowerSeries R), X * g ∈ J ^ (n + 1) → g ∈ J ^ n := by
    intro n g hg
    rw [hJ, GlobalTheory.ChartRing.mem_pow_comap_constantCoeff_iff] at hg ⊢
    intro i
    have := hg (i + 1)
    rwa [coeff_succ_X_mul, Nat.add_sub_add_right] at this
  have hpJ : (p : PowerSeries R) ∈ J := by
    rw [hJ, Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl

  have hlift : ∀ n, ∃ h : PowerSeries R, ev R p (n + 1) h = u n := fun n => Ideal.Quotient.mk_surjective _
  choose H hH using hlift
  have hHu : ∀ n, IsUnit (H n) := fun n =>
    GlobalTheory.ColEx.unit_of_ev R p (n + 1) hR (H n) (by rw [hH]; exact (u n).isUnit)

  set F : ℕ → PowerSeries R := fun k => (smap σ)^[k + 1] ((normOp p)^[k + 1] (H (2 * k + 1))) with hFdef
  have C1 : ∀ k m, m ≤ k → ∃ y : PowerSeries R,
      ev R p (m + 1) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) (F k))
        = u m + ev R p (m + 1) ((p : PowerSeries R) ^ (k + 1 + 1) * y) := by
    intro k m hmk
    obtain ⟨r, hr⟩ := GlobalTheory.ColEx.iter_cong R p σ hF (H (2 * k + 1)) (hHu _) (k + 1) (k - m)
    have h3 := GlobalTheory.ColEx.norm_tower R p hR u hu m (k + 1 + (k - m)) (H (m + (k + 1 + (k - m)))) (hH _)
    have e : m + (k + 1 + (k - m)) = 2 * k + 1 := by omega
    rw [e, hr, map_add] at h3
    refine ⟨-r, ?_⟩
    rw [hFdef]
    dsimp only
    rw [hcancel m (k + 1) _ (by omega), show k + 1 - (m + 1) = k - m by omega, mul_neg, map_neg, ← h3]
    ring
  have C2 : ∀ k, F (k + 1) - F k ∈ J ^ ((k + 1) / 2) := by
    intro k
    have hsmall : ∀ r, 1 ≤ r → r ≤ k + 1 → ∃ y : PowerSeries R,
        ev R p r (F (k + 1) - F k) = ev R p r ((p : PowerSeries R) ^ (k + 2) * y) := by
      intro r h1 h2
      obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      obtain ⟨y1, h1'⟩ := C1 (k + 1) m (by omega)
      obtain ⟨y2, h2'⟩ := C1 k m (by omega)
      have hD : ev R p (m + 1) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) (F (k + 1) - F k))
          = ev R p (m + 1) ((p : PowerSeries R) ^ (k + 2) * ((p : PowerSeries R) * y1 - y2)) := by
        rw [map_sub, map_sub, h1', h2', map_mul, map_mul, map_mul, map_sub, map_mul, map_pow, map_pow]
        ring
      have := GlobalTheory.ColEx.ev_map_congr R p (m + 1) (((σ : R ≃+* R) : R →+* R) ^ (m + 1)) _ _ hD
      rw [hinv, map_mul, map_pow, map_natCast] at this
      exact ⟨_, this⟩
    have hI := GlobalTheory.T.X_mul_mem_span_of_colemanLevels R p hF.dom hF.prime hR (F (k + 1) - F k) (k + 1) (k + 2) hsmall ((k + 1) / 2)
      (by omega) (by omega)
    apply hdivX
    refine (Ideal.span_le.2 ?_) hI
    intro z hz
    rcases hz with rfl | hz
    · exact Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hpJ _)
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact GlobalTheory.ColEx.one_add_X_pow_sub_one_mem R p ((k + 1) / 2)

  have C3 : ∀ n k, n ≤ k → F (2 * k) - F (2 * n) ∈ J ^ n := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => simp
    | succ k hnk ih =>
      have e1 : F (2 * (k + 1)) - F (2 * n) = (F (2 * k + 1 + 1) - F (2 * k + 1)) + (F (2 * k + 1) - F (2 * k))
          + (F (2 * k) - F (2 * n)) := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]; ring
      rw [e1]
      refine add_mem (add_mem ?_ ?_) ih
      · exact Ideal.pow_le_pow_right (by omega) (C2 (2 * k + 1))
      · exact Ideal.pow_le_pow_right (by omega) (C2 (2 * k))
  obtain ⟨f0, hf0⟩ := IsPrecomplete.prec' (I := J) (fun n => F (2 * n)) (fun {a b} hab => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (C3 a b hab))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf0
  have C5 : ∀ m, ev R p (m + 1) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) f0) = u m := by
    intro m
    apply sub_eq_zero.1
    apply GlobalTheory.ColEx.lev_sep R p (m + 1) hR
    intro N
    obtain ⟨y1, hy1⟩ := C1 (2 * (p ^ (m + 1) * N + m + N)) m (by omega)
    have hmem : PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) (f0 - F (2 * (p ^ (m + 1) * N + m + N)))
        ∈ J ^ (p ^ (m + 1) * N) := by
      apply hmapJ
      have hm0 : f0 - F (2 * (p ^ (m + 1) * N + m + N)) ∈ J ^ (p ^ (m + 1) * N + m + N) := by
        rw [← neg_sub]; exact neg_mem (hf0 _)
      exact Ideal.pow_le_pow_right (by omega) hm0
    obtain ⟨y2, hy2⟩ := GlobalTheory.ColEx.ev_of_mem_pow R p (m + 1) N _ hmem
    set n := p ^ (m + 1) * N + m + N
    have e : (p : PowerSeries R) ^ (2 * n + 1 + 1) = (p : PowerSeries R) ^ N * (p : PowerSeries R) ^ (2 * n + 1 + 1 - N) := by
      rw [← pow_add]; congr 1; omega
    refine ⟨y2 + (p : PowerSeries R) ^ (2 * n + 1 + 1 - N) * y1, ?_⟩
    rw [map_sub, map_sub] at hy2
    rw [mul_add, map_add, ← hy2, ← mul_assoc, ← e]
    linear_combination hy1
  have hu0 : IsUnit (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (0 + 1)) f0) :=
    GlobalTheory.ColEx.unit_of_ev R p (0 + 1) hR _ (by rw [C5 0]; exact (u 0).isUnit)
  have hunit : IsUnit f0 := by
    have := hu0.map (PowerSeries.map (((σ : R ≃+* R) : R →+* R) ^ (0 + 1)))
    rwa [hinv] at this
  exact ⟨hunit.unit, fun m => by rw [IsUnit.unit_spec]; exact C5 m⟩

end GlobalTheory.Col
