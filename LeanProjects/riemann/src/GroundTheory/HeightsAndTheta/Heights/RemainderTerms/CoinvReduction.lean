import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms.Coinv

open MvPolynomial Finset

noncomputable section

variable (K : Type*) [Field K] (f n : ℕ)

def bps (m : ℕ) (b : Fin f) : MvPolynomial (Fin f × Fin n) K := ∑ i : Fin n, X (b, i) ^ m

def psumIdeal : Ideal (MvPolynomial (Fin f × Fin n) K) :=
  Ideal.span {P | ∃ m b, 1 ≤ m ∧ m ≤ n ∧ P = bps K f n m b}

variable {K f n}

theorem bps_mem_psumIdeal {m : ℕ} (b : Fin f) (h1 : 1 ≤ m) (h2 : m ≤ n) :
    bps K f n m b ∈ psumIdeal K f n :=
  Ideal.subset_span ⟨m, b, h1, h2, rfl⟩

theorem rename_psum (b : Fin f) (m : ℕ) :
    rename (fun i : Fin n => (b, i)) (psum (Fin n) K m) = bps K f n m b := by
  simp [psum, bps]

variable [CharZero K]

theorem rename_esymm_mem {m : ℕ} (b : Fin f) (h1 : 1 ≤ m) (h2 : m ≤ n) :
    rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m) ∈ psumIdeal K f n := by
  have hN := congrArg (rename (fun i : Fin n => (b, i))) (mul_esymm_eq_sum (Fin n) K m)
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_sum] at hN
  have hmem : ((m : ℕ) : MvPolynomial (Fin f × Fin n) K) *
      rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m) ∈ psumIdeal K f n := by
    rw [hN]
    refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    have ha1 : a.1 + a.2 = m := by simpa using ha.1
    rw [rename_psum]
    exact Ideal.mul_mem_left _ _ (bps_mem_psumIdeal b (by have := ha.2; omega) (by omega))
  have hm : (m : K) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have : rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m) =
      C ((m : K)⁻¹) * (((m : ℕ) : MvPolynomial (Fin f × Fin n) K) *
        rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m)) := by
    rw [← mul_assoc, ← map_natCast C, ← C_mul, inv_mul_cancel₀ hm, C_1, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ hmem

theorem prod_X_add_eq_pow (b : Fin f) :
    (∏ i : Fin n, (Polynomial.X + Polynomial.C
      (Ideal.Quotient.mk (psumIdeal K f n) (X (b, i))))) = Polynomial.X ^ n := by
  set φ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin f × Fin n) K ⧸ psumIdeal K f n :=
    (Ideal.Quotient.mk (psumIdeal K f n)).comp (rename (fun i : Fin n => (b, i))).toRingHom
  have hV := congrArg (Polynomial.map φ) (MvPolynomial.prod_C_add_X_eq_sum_esymm K (Fin n))
  simp only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Fintype.card_fin] at hV
  have hφX : ∀ i : Fin n, φ (X i) = Ideal.Quotient.mk (psumIdeal K f n) (X (b, i)) := by
    intro i; simp [φ]
  simp only [hφX] at hV
  rw [hV, Finset.sum_range_succ']
  have hz : ∀ j ∈ range n, Polynomial.C (φ (esymm (Fin n) K (j + 1))) *
      (Polynomial.X : Polynomial (MvPolynomial (Fin f × Fin n) K ⧸ psumIdeal K f n)) ^ (n - (j + 1)) = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : φ (esymm (Fin n) K (j + 1)) = 0 := by
      simp only [φ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (rename_esymm_mem b (by omega) (by omega))
    rw [this, map_zero, zero_mul]
  rw [Finset.sum_eq_zero hz, zero_add]
  simp [esymm_zero]

variable (K) in
omit [CharZero K] in
theorem psumIdeal_le_ker :
    psumIdeal K f n ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin f × Fin n) K →+* K) := by
  refine Ideal.span_le.mpr ?_
  rintro P ⟨m, b, h1, -, rfl⟩
  simp [bps, constantCoeff_X, zero_pow (show m ≠ 0 by omega)]

theorem psumIdeal_ne_top : psumIdeal K f n ≠ ⊤ := by
  intro h
  have h1 : (1 : MvPolynomial (Fin f × Fin n) K) ∈ RingHom.ker constantCoeff :=
    psumIdeal_le_ker K (h ▸ Submodule.mem_top)
  simp at h1

theorem exists_reduction (b : Fin f) (k : Fin n) :
    ∃ c : ℕ → MvPolynomial ↥(Finset.Ioi k) K,
      X (b, k) ^ ((k : ℕ) + 1) + ∑ j ∈ range ((k : ℕ) + 1),
        rename (fun s : ↥(Finset.Ioi k) => (b, (s : Fin n))) (c j) * X (b, k) ^ j ∈
        psumIdeal K f n := by
  classical
  set ψ := rename (R := K) (fun s : ↥(Finset.Ioi k) => (b, (s : Fin n))) with hψ
  have hinj : Function.Injective (fun s : ↥(Finset.Ioi k) => (b, (s : Fin n))) := by
    intro s t h
    exact Subtype.ext (Prod.ext_iff.mp h).2
  set A' : Polynomial (MvPolynomial ↥(Finset.Ioi k) K) :=
    ∏ s : ↥(Finset.Ioi k), (Polynomial.X + Polynomial.C (X s)) with hA'
  have hA'm : A'.Monic := Polynomial.monic_prod_of_monic _ _ (fun s _ => Polynomial.monic_X_add_C _)
  have hA'deg : A'.natDegree = n - 1 - k := by
    rw [hA', Polynomial.natDegree_prod_of_monic _ _ (fun s _ => Polynomial.monic_X_add_C _)]
    simp [Fin.card_Ioi]
  set Sh' := (Polynomial.X ^ n : Polynomial (MvPolynomial ↥(Finset.Ioi k) K)) /ₘ A' with hSh'
  have hk : (k : ℕ) < n := k.isLt
  have hSdeg : Sh'.natDegree = (k : ℕ) + 1 := by
    rw [hSh', Polynomial.natDegree_divByMonic _ hA'm, Polynomial.natDegree_X_pow, hA'deg]
    omega
  have hSlead : Sh'.leadingCoeff = 1 := by
    rw [hSh', Polynomial.leadingCoeff_divByMonic_of_monic hA'm]
    · simp
    · rw [Polynomial.degree_eq_natDegree hA'm.ne_zero, Polynomial.degree_X_pow, hA'deg]
      exact_mod_cast (by omega : n - 1 - (k : ℕ) ≤ n)

  set I := psumIdeal K f n
  have : Nontrivial (MvPolynomial (Fin f × Fin n) K ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr psumIdeal_ne_top
  set π := Ideal.Quotient.mk I
  have hsplit := prod_X_add_eq_pow (K := K) (f := f) (n := n) b
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin n => k < i)] at hsplit
  have hfilt : Finset.univ.filter (fun i : Fin n => k < i) = Finset.Ioi k := by
    ext i; simp
  rw [hfilt] at hsplit
  have hmapA : A'.map (π.comp ψ.toRingHom) =
      ∏ i ∈ Finset.Ioi k, (Polynomial.X + Polynomial.C (π (X (b, i)))) := by
    rw [hA', Polynomial.map_prod, ← Finset.prod_coe_sort (Finset.Ioi k)]
    simp [hψ, π]
  have key : Sh'.map (π.comp ψ.toRingHom) =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ k < i),
        (Polynomial.X + Polynomial.C (π (X (b, i)))) := by
    rw [hSh', Polynomial.map_divByMonic _ hA'm, Polynomial.map_pow, Polynomial.map_X]
    refine (Polynomial.div_modByMonic_unique _ (0 : Polynomial (MvPolynomial (Fin f × Fin n) K ⧸ I))
      (hA'm.map (π.comp ψ.toRingHom)) ⟨?_, ?_⟩).1
    · rw [zero_add, hmapA, hsplit]
    · rw [Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (fun h => (hA'm.map (π.comp ψ.toRingHom)).ne_zero
        (Polynomial.degree_eq_bot.mp h))
  have hev : π (Polynomial.eval (-X (b, k)) (Sh'.map ψ.toRingHom)) = 0 := by
    rw [← Polynomial.eval₂_at_apply π, ← Polynomial.eval_map, Polynomial.map_map, key,
      Polynomial.eval_prod]
    refine Finset.prod_eq_zero (i := k) (by simp) ?_
    simp
  have hmem : Polynomial.eval (-X (b, k)) (Sh'.map ψ.toRingHom) ∈ I :=
    Ideal.Quotient.eq_zero_iff_mem.mp hev

  refine ⟨fun j => (-1) ^ ((k : ℕ) + 1 + j) * Sh'.coeff j, ?_⟩
  have hdegmap : (Sh'.map ψ.toRingHom).natDegree = (k : ℕ) + 1 := by
    rw [Polynomial.natDegree_map_eq_of_injective (rename_injective _ hinj), hSdeg]
  rw [Polynomial.eval_eq_sum_range, hdegmap, Finset.sum_range_succ] at hmem
  have htop : (Sh'.map ψ.toRingHom).coeff ((k : ℕ) + 1) = 1 := by
    rw [Polynomial.coeff_map, ← hSdeg]
    change ψ (Sh'.leadingCoeff) = 1
    rw [hSlead, map_one]
  rw [htop, one_mul] at hmem
  have := Ideal.mul_mem_left I ((-1) ^ ((k : ℕ) + 1)) hmem
  convert this using 1
  rw [mul_add, Finset.mul_sum, neg_pow (X (b, k) : MvPolynomial (Fin f × Fin n) K), ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_mul, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_map, neg_pow (X (b, k) : MvPolynomial (Fin f × Fin n) K)]
  simp only [map_mul, map_pow, map_neg, map_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

end

end GroundTheory.Heights₂.Heights.RestTerms.Coinv
