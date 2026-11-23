import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Polynomial IntermediateField

namespace GlobalTheory.LadicDenom

theorem norm_natCast_padicComplex (l : ℕ) [Fact l.Prime] (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  have h : (n : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (n : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_ratCast_padicComplex (l : ℕ) [Fact l.Prime] (q : ℚ) : ‖(q : ℂ_[l])‖ = ‖(q : ℚ_[l])‖ := by
  have h : (q : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_prime_padicComplex (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_padicComplex, Padic.norm_p]

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem not_dvd_den_of_norm_le_one (l : ℕ) [hl : Fact l.Prime] (q : ℚ) (h : ‖(q : ℚ_[l])‖ ≤ 1) : ¬ l ∣ q.den := by
  intro hd
  have hnum : ‖(q.num : ℚ_[l])‖ = 1 := by
    have hc : l.Coprime q.num.natAbs := (Nat.Prime.coprime_iff_not_dvd hl.out).2 fun hn =>
      hl.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes q.reduced hn hd)
    rcases Int.natAbs_eq q.num with e | e
    · rw [e, Int.cast_natCast]; exact Padic.norm_natCast_eq_one_iff.2 hc
    · rw [e, Int.cast_neg, Int.cast_natCast, norm_neg]; exact Padic.norm_natCast_eq_one_iff.2 hc
  have hden : ‖(q.den : ℚ_[l])‖ < 1 := by
    refine lt_of_le_of_ne ?_ fun e => ?_
    · exact_mod_cast Padic.norm_int_le_one (q.den : ℤ)
    · have := Padic.norm_natCast_eq_one_iff.1 e
      exact hl.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hd)
  have e : (q : ℚ_[l]) * (q.den : ℚ_[l]) = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have e2 := congrArg norm e
  rw [norm_mul, hnum] at e2
  have : ‖(q : ℚ_[l])‖ * ‖(q.den : ℚ_[l])‖ < 1 :=
    (mul_le_of_le_one_left (norm_nonneg _) h).trans_lt hden
  exact this.ne e2

set_option synthInstance.maxHeartbeats 400000 in

theorem norm_root_le_one (l : ℕ) [Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) (β : ℂ_[l]) (hβ : β ∈ (minpoly ℚ α).aroots ℂ_[l]) :
    ‖β‖ ≤ 1 := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  let φ := (algHomAdjoinIntegralEquiv ℚ hα).symm ⟨β, hβ⟩
  letI : Algebra ℚ⟮α⟯ ℂ_[l] := φ.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ⟮α⟯ (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) _
  let ψ : algebraicClosure ℚ ℂ →ₐ[ℚ⟮α⟯] ℂ_[l] := IsAlgClosed.lift
  have e : ψ α = β := by
    have h1 := ψ.commutes (AdjoinSimple.gen ℚ α)
    rw [AdjoinSimple.algebraMap_gen] at h1
    rw [h1]
    exact algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hα ⟨β, hβ⟩
  rw [← e]
  exact h ψ.toRingHom

theorem coeff_norm_le_one (l : ℕ) [Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) (i : ℕ) :
    ‖(((minpoly ℚ α).coeff i : ℚ) : ℂ_[l])‖ ≤ 1 := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set P := (minpoly ℚ α).map (algebraMap ℚ ℂ_[l]) with hP
  let S := (NormedField.valuation (K := ℂ_[l])).integer
  have memS : ∀ z : ℂ_[l], z ∈ S ↔ ‖z‖ ≤ 1 := by
    intro z
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast Iff.rfl
  have hmon : P.Monic := (minpoly.monic hα).map _
  have hroots : ∀ β ∈ P.roots, β ∈ S := fun β hβ => (memS β).2 (norm_root_le_one l α h β hβ)
  have hc : (((minpoly ℚ α).coeff i : ℚ) : ℂ_[l]) = P.coeff i := by
    rw [hP, coeff_map, eq_ratCast]
  rw [hc, ← memS]
  by_cases hi : i ≤ P.natDegree
  · rw [coeff_eq_esymm_roots_of_card IsAlgClosed.card_roots_eq_natDegree hi, hmon.leadingCoeff, one_mul]
    refine S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) ?_
    unfold Multiset.esymm
    refine S.multiset_sum_mem _ fun z hz => ?_
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hz
    exact S.multiset_prod_mem _ fun w hw => hroots w (Multiset.mem_of_le (Multiset.mem_powersetCard.1 ht).1 hw)
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
    exact S.zero_mem

theorem intAt_of_forall_norm_le_one (l : ℕ) [hl : Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) : IntAt l (α : ℂ) := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set p := minpoly ℚ α with hp
  have hmon : p.Monic := minpoly.monic hα
  have hden : ∀ i, ¬ l ∣ (p.coeff i).den := fun i =>
    not_dvd_den_of_norm_le_one l _ (by rw [← norm_ratCast_padicComplex]; exact coeff_norm_le_one l α h i)
  set D : ℕ := ∏ i ∈ Finset.range p.natDegree, (p.coeff i).den with hD
  have hDc : D.Coprime l := Nat.Coprime.prod_left fun i _ =>
    ((Nat.Prime.coprime_iff_not_dvd hl.out).2 (hden i)).symm
  refine ⟨D, hDc, ?_⟩
  set q := p.scaleRoots (D : ℚ) with hq
  have hql : q ∈ lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [hq, coeff_scaleRoots]
    rcases lt_trichotomy n p.natDegree with hn | hn | hn
    · obtain ⟨e, he⟩ : (p.coeff n).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hn)
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - n = k + 1 := ⟨p.natDegree - n - 1, by omega⟩
      have h1 : p.coeff n * ((p.coeff n).den : ℚ) = (p.coeff n).num := Rat.mul_den_eq_num _
      refine ⟨(p.coeff n).num * e * D ^ k, ?_⟩
      simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [hk, pow_succ, ← h1]
      have h2 : (D : ℚ) = (p.coeff n).den * e := by exact_mod_cast he
      rw [h2]
      ring
    · refine ⟨1, ?_⟩
      rw [hn, hmon.coeff_natDegree, Nat.sub_self, pow_zero, mul_one, map_one]
    · refine ⟨0, ?_⟩
      rw [coeff_eq_zero_of_natDegree_lt hn, zero_mul, map_zero]
  have hqm : q.Monic := by
    rw [Monic, hq, leadingCoeff_scaleRoots]; exact hmon
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hql hqm
  have hroot : aeval ((D : algebraicClosure ℚ ℂ) * α) q = 0 := by
    have := scaleRoots_aeval_eq_zero (r := (D : ℚ)) (minpoly.aeval ℚ α)
    simpa using this
  have hint : IsIntegral ℤ ((D : algebraicClosure ℚ ℂ) * α) := by
    refine ⟨Q, hQm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ, algebraMap_int_eq, hQ]
    exact hroot
  have := map_isIntegral_int (algebraicClosure ℚ ℂ).val.toRingHom hint
  simpa using this

theorem valGe_iff_forall_sz (l : ℕ) [hl : Fact l.Prime] (r : ℝ) (x : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r x ↔ ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], Sz l lam r x := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  constructor
  · intro hv lam
    obtain ⟨N, hN, hi⟩ := hv ⌈r⌉ 1 one_pos (by simpa using Int.le_ceil r)
    have hN0 : N ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hN
      exact hl.out.one_lt.ne' hN
    have hmem : x ∈ algebraicClosure ℚ ℂ := by
      have h1 : (N : ℂ) * ((l : ℂ) ^ ⌈r⌉ * x ^ 1) ∈ algebraicClosure ℚ ℂ :=
        mem_algebraicClosure_iff.2 (hi.tower_top (A := ℚ)).isAlgebraic
      have h2 : ((N : ℂ) * (l : ℂ) ^ ⌈r⌉) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 hN0) (zpow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
      have h3 : x = ((N : ℂ) * ((l : ℂ) ^ ⌈r⌉ * x ^ 1)) * ((N : ℂ) * (l : ℂ) ^ ⌈r⌉)⁻¹ := by
        rw [pow_one, ← mul_assoc, mul_right_comm, mul_inv_cancel₀ h2, one_mul]
      rw [h3]
      exact mul_mem h1 (inv_mem (mul_mem (IntermediateField.natCast_mem _ _) (zpow_mem (IntermediateField.natCast_mem _ _) _)))
    refine ⟨hmem, ?_⟩
    set t := ‖lam ⟨x, hmem⟩‖ with ht
    have key : ∀ (m : ℤ) (n : ℕ), 0 < n → r ≤ (m : ℝ) / n → t ^ n ≤ (l : ℝ) ^ m := by
      intro m n hn hmn
      obtain ⟨N, hN, hi⟩ := hv m n hn hmn
      set β : algebraicClosure ℚ ℂ := (N : algebraicClosure ℚ ℂ) * ((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n)
      have hiβ : IsIntegral ℤ β := by
        refine (isIntegral_algHom_iff ((algebraicClosure ℚ ℂ).val.restrictScalars ℤ) Subtype.val_injective).1 ?_
        have e : ((algebraicClosure ℚ ℂ).val.restrictScalars ℤ) β = (N : ℂ) * ((l : ℂ) ^ m * x ^ n) :=
          Complex.ext rfl rfl
        rw [e]; exact hi
      have h1 := norm_le_one_of_isIntegral (map_isIntegral_int lam hiβ)
      simp only [β, map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow] at h1
      rw [norm_natCast_padicComplex, Padic.norm_natCast_eq_one_iff.2 hN.symm, norm_prime_padicComplex, one_mul,
        inv_zpow', zpow_neg, inv_mul_le_iff₀ (zpow_pos hl0 m), mul_one] at h1
      exact h1
    by_contra hgt
    rw [not_le] at hgt
    have htp : 0 < t := (Real.rpow_pos_of_pos hl0 r).trans hgt
    have hr : r < Real.logb l t := (Real.lt_logb_iff_rpow_lt hl1 htp).2 hgt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr
    have hq3 : (l : ℝ) ^ (q : ℝ) < t := (Real.lt_logb_iff_rpow_lt hl1 htp).1 hq2
    have hqe : (q : ℝ) = (q.num : ℝ) / (q.den : ℕ) := by exact_mod_cast (Rat.num_div_den q).symm
    have hk := key q.num q.den q.den_pos (by rw [← hqe]; exact hq1.le)
    have h4 : ((l : ℝ) ^ (q : ℝ)) ^ q.den < t ^ q.den :=
      pow_lt_pow_left₀ hq3 (Real.rpow_nonneg hl0.le _) q.den_pos.ne'
    have h5 : ((l : ℝ) ^ (q : ℝ)) ^ q.den = (l : ℝ) ^ q.num := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le, ← Real.rpow_intCast, hqe,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.2 q.den_pos.ne')]
    rw [h5] at h4
    exact absurd hk (not_le.2 h4)
  · intro h
    let lam₀ : algebraicClosure ℚ ℂ →+* ℂ_[l] := (IsAlgClosed.lift : algebraicClosure ℚ ℂ →ₐ[ℚ] ℂ_[l]).toRingHom
    obtain ⟨hmem, -⟩ := h lam₀
    intro m n hn hmn
    have hmn' : r * n ≤ m := by rwa [le_div_iff₀ (Nat.cast_pos.2 hn)] at hmn
    have hb : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l],
        ‖lam ((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n)‖ ≤ 1 := by
      intro lam
      obtain ⟨h', hle⟩ := h lam
      rw [map_mul, map_zpow₀, map_pow, map_natCast, norm_mul, norm_zpow, norm_pow, norm_prime_padicComplex,
        inv_zpow', zpow_neg]
      have h2 : ‖lam ⟨x, hmem⟩‖ ^ n ≤ (l : ℝ) ^ m := by
        calc ‖lam ⟨x, hmem⟩‖ ^ n ≤ ((l : ℝ) ^ r) ^ n := pow_le_pow_left₀ (norm_nonneg _) hle n
          _ = (l : ℝ) ^ (r * n) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
          _ ≤ (l : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hl1.le hmn'
          _ = (l : ℝ) ^ m := Real.rpow_intCast _ _
      rw [inv_mul_le_iff₀ (zpow_pos hl0 m), mul_one]
      exact h2
    have := intAt_of_forall_norm_le_one l _ hb
    have e : (((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n : algebraicClosure ℚ ℂ) : ℂ) = (l : ℂ) ^ m * x ^ n :=
      Complex.ext rfl rfl
    rwa [e] at this

end GlobalTheory.LadicDenom
