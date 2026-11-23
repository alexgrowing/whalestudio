import Mathlib

namespace Formalism.L2.Pj.CurveCount

open MvPolynomial

theorem eval₂_mul_homog {R S σ : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (c : S) (g : σ → S)
    {P : MvPolynomial σ R} {k : ℕ} (hP : P.IsHomogeneous k) :
    P.eval₂ f (fun i => c * g i) = c ^ k * P.eval₂ f g := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = k := by
    have h := hP (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem aeval_div_homog {K L σ : Type*} [Field K] [Field L] [Algebra K L] (g : σ → L) (c : L)
    {P : MvPolynomial σ K} {k : ℕ} (hP : P.IsHomogeneous k) :
    aeval (fun i => g i / c) P = c⁻¹ ^ k * aeval g P := by
  have h := eval₂_mul_homog (algebraMap K L) c⁻¹ g hP
  show MvPolynomial.eval₂ (algebraMap K L) (fun i => g i / c) P =
    c⁻¹ ^ k * MvPolynomial.eval₂ (algebraMap K L) g P
  rw [← h]
  congr 1
  funext i
  rw [div_eq_mul_inv, mul_comm]

theorem exists_indep_ratios {K κ : Type*} [Field K] [Field κ] [Algebra K κ] {N D : ℕ} (x : Fin N → κ) (a : Fin N)
    (hxa : x a ≠ 0) (t : Fin (D + 1) × Fin N → κ) (ht : AlgebraicIndependent K t)
    (hlin : ∀ i : Fin D, ∑ k, t (i.succ, k) * x k = 0) (hlin0 : ∑ k, t (0, k) * x k = 1) :
    ∃ s : Finset κ, s.card = D ∧ (↑s : Set κ) ⊆ Set.range (fun i => x i / x a) ∧
      AlgebraicIndepOn K id (↑s : Set κ) := by
  classical
  have : FaithfulSMul K κ := (faithfulSMul_iff_algebraMap_injective K κ).mpr (algebraMap K κ).injective
  set r : Fin N → κ := fun i => x i / x a with hr
  let t2 : Fin (D + 1) × ↥(Finset.univ.erase a) → κ := fun p => t (p.1, p.2.1)
  set T2 : Set κ := insert (x a)⁻¹ (Set.range t2) with hT2
  set S : Set κ := Set.range r ∪ T2 with hS
  have hc : ∀ i : Fin (D + 1), ∑ k, t (i, k) * x k = if i = 0 then 1 else 0 := by
    intro i
    cases i using Fin.cases with
    | zero => simpa using hlin0
    | succ i => simpa [Fin.succ_ne_zero] using hlin i
  have hrS : ∀ k, r k ∈ Algebra.adjoin K S := fun k => Algebra.subset_adjoin (Or.inl ⟨k, rfl⟩)
  have hzS : (x a)⁻¹ ∈ Algebra.adjoin K S := Algebra.subset_adjoin (Or.inr (Set.mem_insert _ _))
  have htS : ∀ i k, k ≠ a → t (i, k) ∈ Algebra.adjoin K S := fun i k hk =>
    Algebra.subset_adjoin (Or.inr (Set.mem_insert_of_mem _
      ⟨(i, ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩⟩), rfl⟩))
  have hmem : ∀ p, t p ∈ Algebra.adjoin K S := by
    rintro ⟨i, k⟩
    by_cases hk : k = a
    · rw [hk]
      have e : t (i, a) = (if i = 0 then 1 else 0) * (x a)⁻¹ - ∑ l ∈ Finset.univ.erase a, t (i, l) * r l := by
        have h := hc i
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h
        rw [← h, add_mul, Finset.sum_mul, add_sub_assoc, ← Finset.sum_sub_distrib]
        simp only [hr, div_eq_mul_inv, mul_assoc, sub_self, Finset.sum_const_zero, add_zero,
          mul_inv_cancel₀ hxa, mul_one]
      rw [e]
      refine Subalgebra.sub_mem _ (Subalgebra.mul_mem _ ?_ hzS)
        (Subalgebra.sum_mem _ fun l hl => Subalgebra.mul_mem _ (htS i l (Finset.ne_of_mem_erase hl)) (hrS l))
      split_ifs
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · exact htS i k hk
  let M := AlgebraicIndependent.matroid K κ
  have hI : M.Indep (Set.range t) := AlgebraicIndependent.matroid_indep_iff.mpr ht.to_subtype_range
  have hIS : Set.range t ⊆ M.closure S := by
    rintro _ ⟨p, rfl⟩
    rw [AlgebraicIndependent.matroid_closure_eq]
    exact isAlgebraic_algebraMap (⟨t p, hmem p⟩ : Algebra.adjoin K S)
  have h1 := hI.encard_le_eRk_of_subset hIS
  rw [M.eRk_closure_eq] at h1
  have h2 := M.eRk_union_le_eRk_add_eRk (Set.range r) T2
  have h3 : M.eRk T2 ≤ ((D + 1) * (N - 1) + 1 : ℕ) := by
    refine (M.eRk_le_encard T2).trans ((Set.encard_insert_le _ _).trans ?_)
    have h4 : (Set.range t2).encard ≤ ((D + 1) * (N - 1) : ℕ) := by
      rw [← Set.image_univ]
      refine (Set.encard_image_le _ _).trans ?_
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add h4 le_rfl
  have h5 : (((D + 1) * N : ℕ) : ℕ∞) ≤ (Set.range t).encard := by
    have := ht.injective.encard_range
    rwa [ENat.card_eq_coe_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
  have hfin : M.eRk (Set.range r) ≠ ⊤ :=
    ne_top_of_le_ne_top (Set.finite_range r).encard_lt_top.ne (M.eRk_le_encard _)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hineq : (D + 1) * N ≤ n + ((D + 1) * (N - 1) + 1) := by
    have := h5.trans (h1.trans (h2.trans (add_le_add le_rfl h3)))
    rw [← hn, ← Nat.cast_add, Nat.cast_le] at this
    exact this
  have hN : (D + 1) * N = (D + 1) * (N - 1) + (D + 1) := by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by have := a.2; omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hDn : D ≤ n := by
    rw [hN] at hineq
    generalize (D + 1) * (N - 1) = X at hineq
    omega
  obtain ⟨B, hB⟩ := M.exists_isBasis (Set.range r) (Set.subset_univ _)
  have hDB : ((D : ℕ) : ℕ∞) ≤ B.encard := by
    rw [hB.encard_eq_eRk, ← hn]
    exact_mod_cast hDn
  obtain ⟨B', hB'sub, hB'card⟩ := Set.exists_subset_encard_eq hDB
  have hB'fin : B'.Finite := Set.finite_of_encard_eq_coe hB'card
  refine ⟨hB'fin.toFinset, ?_, ?_, ?_⟩
  · have := Set.encard_coe_eq_coe_finsetCard hB'fin.toFinset
    rw [Set.Finite.coe_toFinset, hB'card] at this
    exact_mod_cast this.symm
  · rw [Set.Finite.coe_toFinset]
    exact hB'sub.trans hB.subset
  · rw [Set.Finite.coe_toFinset]
    exact AlgebraicIndependent.matroid_indep_iff.mp (hB.indep.subset hB'sub)

theorem countCore {K κ Ω : Type*} [Field K] [Field κ] [Field Ω] [Algebra K κ] [Algebra K Ω] {N D : ℕ}
    (v : Fin N → Ω) (x : Fin N → κ) (a : Fin N) (hva : v a ≠ 0) (hxa : x a ≠ 0)
    (htr : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun i => v i / v a)) ≤ D)
    (htrans : ∀ Q : MvPolynomial (Fin N) K, aeval (fun i => v i / v a) Q = 0 → aeval (fun i => x i / x a) Q = 0)
    (t : Fin (D + 1) × Fin N → κ) (ht : AlgebraicIndependent K t)
    (hlin : ∀ i : Fin D, ∑ k, t (i.succ, k) * x k = 0) (hlin0 : ∑ k, t (0, k) * x k = 1)
    (P : MvPolynomial (Fin N) K) {k : ℕ} (hP : P.IsHomogeneous k) (hPv : aeval v P ≠ 0) :
    aeval x P ≠ 0 := by
  classical
  intro hxP
  set ρ : Fin N → Ω := fun i => v i / v a with hρ
  set σ : Fin N → κ := fun i => x i / x a with hσ
  have hα0 : aeval ρ P ≠ 0 := by
    rw [hρ, aeval_div_homog v (v a) hP]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hva)) hPv
  have hσP : aeval σ P = 0 := by
    rw [hσ, aeval_div_homog x (x a) hP, hxP, mul_zero]
  obtain ⟨s, hscard, hsub, hind⟩ := exists_indep_ratios (K := K) x a hxa t ht hlin hlin0
  have hf : ∀ e : s, ∃ i, σ i = (e : κ) := fun e => hsub e.2
  choose f hfe using hf
  have hy : AlgebraicIndependent K (fun e : s => (e : κ)) := hind
  have h3 : (σ ∘ f) = fun e : s => (e : κ) := funext hfe
  have huind : AlgebraicIndependent K (ρ ∘ f) := by
    rw [algebraicIndependent_iff]
    intro Q hQ
    have h1 : aeval ρ (rename f Q) = 0 := by rw [aeval_rename]; exact hQ
    have h2 := htrans (rename f Q) h1
    rw [aeval_rename, h3] at h2
    exact (algebraicIndependent_iff.mp hy) Q h2
  have hρA : ∀ i, ρ i ∈ IntermediateField.adjoin K (Set.range ρ) :=
    fun i => IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  let ρA : Fin N → IntermediateField.adjoin K (Set.range ρ) := fun i => ⟨ρ i, hρA i⟩
  have hvalρ : ∀ Q : MvPolynomial (Fin N) K,
      IntermediateField.val _ (aeval ρA Q) = aeval ρ Q := by
    intro Q
    induction Q using MvPolynomial.induction_on
    next c =>
      simp only [MvPolynomial.aeval_C, AlgHom.commutes]
    next p q hp hq =>
      rw [map_add, map_add, map_add, hp, hq]
    next p i hp =>
      rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      rfl
  have hnot : ¬ AlgebraicIndependent K (fun o : Option s => o.elim (aeval ρ P) (ρ ∘ f)) := by
    intro hI
    let w : Option s → IntermediateField.adjoin K (Set.range ρ) :=
      fun o => o.elim (aeval ρA P) (fun e => ρA (f e))
    have hcomp : (IntermediateField.val _) ∘ w = fun o : Option s => o.elim (aeval ρ P) (ρ ∘ f) := by
      funext o
      cases o with
      | none => exact hvalρ P
      | some e => rfl
    have hw : AlgebraicIndependent K w := by
      apply AlgebraicIndependent.of_comp (IntermediateField.val _)
      rw [hcomp]
      exact hI
    have hcard := hw.lift_cardinalMk_le_trdeg.trans (Cardinal.lift_le.mpr htr)
    simp [Cardinal.mk_fintype, Fintype.card_option, hscard] at hcard
  have halg : IsAlgebraic (Algebra.adjoin K (Set.range (ρ ∘ f))) (aeval ρ P) := by
    by_contra hna
    exact hnot ((huind.option_iff_transcendental _).mpr hna)
  set α := aeval ρ P with hαdef
  have hex : ∃ n, ∃ p : Polynomial (Algebra.adjoin K (Set.range (ρ ∘ f))),
      p ≠ 0 ∧ Polynomial.aeval α p = 0 ∧ p.natDegree = n := by
    obtain ⟨p, hp0, hp⟩ := halg
    exact ⟨_, p, hp0, hp, rfl⟩
  obtain ⟨p, hp0, hpα, hpn⟩ := Nat.find_spec hex
  have hc0 : p.coeff 0 ≠ 0 := by
    intro hc
    have hdec : Polynomial.X * p.divX = p := by
      have h0 := Polynomial.X_mul_divX_add p
      rw [hc, map_zero, add_zero] at h0
      exact h0
    have hd0 : p.divX ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdec
      exact hp0 hdec.symm
    have hdα : Polynomial.aeval α p.divX = 0 := by
      have h1 : Polynomial.aeval α p = α * Polynomial.aeval α p.divX := by
        conv_lhs => rw [← hdec]
        rw [map_mul, Polynomial.aeval_X]
      rw [hpα] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left hα0
    have hdeg : p.divX.natDegree < p.natDegree := by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
      have hn0 : p.natDegree ≠ 0 := by
        intro h0
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero] at hp0
        exact hp0 rfl
      omega
    exact Nat.find_min hex (hpn ▸ hdeg) ⟨p.divX, hd0, hdα, rfl⟩
  have hQ : ∀ c : Algebra.adjoin K (Set.range (ρ ∘ f)), ∃ Q : MvPolynomial s K,
      aeval (ρ ∘ f) Q = (c : Ω) := by
    intro c
    have hc : (c : Ω) ∈ (MvPolynomial.aeval (R := K) (ρ ∘ f)).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact c.2
    obtain ⟨Q, hQ⟩ := hc
    exact ⟨Q, hQ⟩
  choose Qc hQc using hQ
  have hT : aeval ρ (∑ j ∈ Finset.range (p.natDegree + 1), rename f (Qc (p.coeff j)) * P ^ j) = 0 := by
    rw [map_sum]
    simp only [map_mul, map_pow, aeval_rename, hQc]
    rw [← hpα, Polynomial.aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    rfl
  have hT2 := htrans _ hT
  rw [map_sum, Finset.sum_range_succ'] at hT2
  simp only [map_mul, map_pow, aeval_rename, hσP, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, mul_one] at hT2
  rw [h3] at hT2
  have h4 := (algebraicIndependent_iff.mp hy) _ hT2
  have h5 := hQc (p.coeff 0)
  rw [h4, map_zero] at h5
  apply hc0
  apply Subtype.ext
  simpa using h5.symm

end Formalism.L2.Pj.CurveCount
