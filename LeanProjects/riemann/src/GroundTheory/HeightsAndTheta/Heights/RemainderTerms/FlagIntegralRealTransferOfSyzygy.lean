import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealRootRingToRealAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace RestBoundEq

theorem summable_signed (p : ℕ) (hp : 2 ≤ p) (k : ℕ) (hk : 1 ≤ k) (R : ℚ) (ε : ℕ → ℚ)
    (hε : ∀ n, ε n = 1 ∨ ε n = -1) :
    Summable (fun n : ℕ => ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((ε n * R : ℚ) : ℝ)) := by
  set q : ℝ := ((p : ℝ) ^ k)⁻¹ with hq
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp1 (by omega))
  have hpow : ∀ n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ = q * q ^ n := fun n => by
    rw [hq, ← pow_succ', mul_comm, pow_mul, inv_pow]
  refine Summable.of_norm_bounded (g := fun n => q * q ^ n * |(R : ℝ)|)
    (((summable_geometric_of_lt_one hq0 hq1).mul_left q).mul_right _) (fun n => ?_)
  rw [hpow, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs]
  rcases hε n with h | h <;> simp [h]

theorem flagIntegral_add_smul (f N : ℕ) (A B : RootRing f N) (t : ℚ) :
    flagIntegral f N (A + t • B) = flagIntegral f N A + t * flagIntegral f N B := by
  rw [flagIntegral, flagIntegral, flagIntegral, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun α _ => ?_
  rw [coeff_add, coeff_smul, smul_eq_mul]
  ring

theorem syzygy_term_zero (hA : RestBound.Statement) (f r a : ℕ) (c : SmallBlock)
    (hf : 1 ≤ f) (hr : 1 ≤ r) (ha : 1 ≤ a) (S : ℕ → Fin f → RootRing f (r + a))
    (hS : IsPowerSumDecomposition f (r + a) 0 S) (τ τ' : Fin f) (m : ℕ) (hm2 : 2 ≤ m)
    (hmN : m ≤ r + a) :
    flagIntegral f (r + a) (smallPowerSum f r a c (m - 1) τ' * S m τ) = 0 := by
  set B₀ : ℝ := 4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2
  obtain ⟨⟨Q₀, hQ₀⟩, hall⟩ := hA f r a c B₀ hf hr ha le_rfl
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (⌈B₀⌉₊ + 1)
  have hBp : B₀ < p := by
    have := Nat.le_ceil B₀
    have h2 : ((⌈B₀⌉₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hpB
    push_cast at h2
    linarith
  have hp2 : 2 ≤ p := hp.two_le
  set Bnd : ℝ := 1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|

  set Qt : ℚ → ℕ → Fin f → RootRing f (r + a) := fun t k σ => Q₀ k σ + t • S k σ with hQt
  have hQtd : ∀ t, IsPowerSumDecomposition f (r + a) (restPolynomial f r a c) (Qt t) := by
    intro t
    unfold IsPowerSumDecomposition at hQ₀ hS ⊢
    simp only [hQt, mul_add, mul_smul_comm, sum_add_distrib, ← smul_sum, ← hS, smul_zero,
      add_zero]
    exact hQ₀
  set s : ℕ → ℕ → Fin f → Fin f := fun _ _ _ => τ'
  set e₁ : ℕ → ℕ → Fin f → ℕ → ℚ := fun _ _ _ _ => 1
  set e₂ : ℕ → ℕ → Fin f → ℕ → ℚ := fun _ n σ k => if n = 1 ∧ σ = τ ∧ k = m then -1 else 1
  have he₁ : ∀ q n σ k, e₁ q n σ k = 1 ∨ e₁ q n σ k = -1 := fun _ _ _ _ => Or.inl rfl
  have he₂ : ∀ q n σ k, e₂ q n σ k = 1 ∨ e₂ q n σ k = -1 := fun _ n σ k => by
    simp only [e₂]; split_ifs <;> simp

  have hone : ∀ g : ℕ → ℝ,
      ∑' q : {q : ℕ // q ∈ ({p} : Set ℕ) ∧ q.Prime ∧ B₀ < q}, g q = g p := by
    intro g
    rw [tsum_eq_single (⟨p, rfl, hp, hBp⟩ : {q : ℕ // q ∈ ({p} : Set ℕ) ∧ q.Prime ∧ B₀ < q})
      (fun b hb => absurd (Subtype.ext (Set.mem_singleton_iff.1 b.2.1)) hb)]
  have hbd : ∀ t (e : ℕ → ℕ → Fin f → ℕ → ℚ), (∀ q n σ k, e q n σ k = 1 ∨ e q n σ k = -1) →
      |restPrimeModel f r a c (Qt t) s e p| ≤ Bnd := by
    intro t e he
    have := (hall (Qt t) (hQtd t) s e he {p}).2
    rwa [hone] at this

  have hdiff : ∀ Q : ℕ → Fin f → RootRing f (r + a),
      restPrimeModel f r a c Q s e₁ p - restPrimeModel f r a c Q s e₂ p =
        Real.log p * (2 * ((p : ℝ) ^ m)⁻¹ *
          ((restTerm f (r + a) Q m τ (smallPowerSum f r a c (m - 1) τ') : ℚ) : ℝ)) := by
    intro Q
    have hin : ∀ σ : Fin f, ∀ k ∈ Icc 2 (r + a),
        (∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
            ((e₁ p (n + 1) σ k * restTerm f (r + a) Q k σ
              (smallPowerSum f r a c (k - 1) (s p (n + 1) σ)) : ℚ) : ℝ)) -
          ∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
            ((e₂ p (n + 1) σ k * restTerm f (r + a) Q k σ
              (smallPowerSum f r a c (k - 1) (s p (n + 1) σ)) : ℚ) : ℝ) =
        if σ = τ ∧ k = m then 2 * ((p : ℝ) ^ m)⁻¹ *
          ((restTerm f (r + a) Q m τ (smallPowerSum f r a c (m - 1) τ') : ℚ) : ℝ) else 0 := by
      intro σ k hk
      have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.1 hk).1; omega
      have hs' : ∀ n : ℕ, s p (n + 1) σ = τ' := fun _ => rfl
      simp only [hs']
      have hs1 := summable_signed p hp2 k hk1
        (restTerm f (r + a) Q k σ (smallPowerSum f r a c (k - 1) τ'))
        (fun n => e₁ p (n + 1) σ k) (fun n => he₁ p (n + 1) σ k)
      have hs2 := summable_signed p hp2 k hk1
        (restTerm f (r + a) Q k σ (smallPowerSum f r a c (k - 1) τ'))
        (fun n => e₂ p (n + 1) σ k) (fun n => he₂ p (n + 1) σ k)
      rw [← hs1.tsum_sub hs2]
      have h0 : ∀ n : ℕ, n ≠ 0 →
          ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((e₁ p (n + 1) σ k *
            restTerm f (r + a) Q k σ (smallPowerSum f r a c (k - 1) τ') : ℚ) : ℝ) -
          ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((e₂ p (n + 1) σ k *
            restTerm f (r + a) Q k σ (smallPowerSum f r a c (k - 1) τ') : ℚ) : ℝ) = 0 := by
        intro n hn
        have hn1 : n + 1 ≠ 1 := by omega
        simp only [e₁, e₂, hn1, false_and, if_false, sub_self]
      rw [tsum_eq_single 0 h0]
      by_cases hστ : σ = τ ∧ k = m
      · obtain ⟨rfl, rfl⟩ := hστ
        simp only [e₁, e₂, zero_add, and_self, if_true, zero_add, one_mul]
        push_cast
        ring
      · have hne : ¬ (0 + 1 = 1 ∧ σ = τ ∧ k = m) := fun h => hστ h.2
        rw [if_neg hστ]
        simp only [e₁, e₂, if_neg hne]
        push_cast
        ring
    rw [restPrimeModel, restPrimeModel, ← mul_sub, ← sum_sub_distrib]
    congr 1
    have hσ : ∀ σ ∈ (univ : Finset (Fin f)), (∑ k ∈ Icc 2 (r + a), ∑' n : ℕ,
        ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((e₁ p (n + 1) σ k * restTerm f (r + a) Q k σ
          (smallPowerSum f r a c (k - 1) (s p (n + 1) σ)) : ℚ) : ℝ)) -
        ∑ k ∈ Icc 2 (r + a), ∑' n : ℕ,
        ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((e₂ p (n + 1) σ k * restTerm f (r + a) Q k σ
          (smallPowerSum f r a c (k - 1) (s p (n + 1) σ)) : ℚ) : ℝ) =
        ∑ k ∈ Icc 2 (r + a), if σ = τ ∧ k = m then 2 * ((p : ℝ) ^ m)⁻¹ *
          ((restTerm f (r + a) Q m τ (smallPowerSum f r a c (m - 1) τ') : ℚ) : ℝ) else 0 :=
      fun σ _ => by rw [← sum_sub_distrib]; exact sum_congr rfl (hin σ)
    rw [sum_congr rfl hσ]
    simp only [ite_and]
    rw [Fintype.sum_eq_single τ (fun σ hσ => by simp [hσ])]
    simp only [if_true]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_Icc.2 ⟨hm2, hmN⟩)]

  have hlin : ∀ t : ℚ, restTerm f (r + a) (Qt t) m τ (smallPowerSum f r a c (m - 1) τ') =
      restTerm f (r + a) Q₀ m τ (smallPowerSum f r a c (m - 1) τ') +
        t * restTerm f (r + a) S m τ (smallPowerSum f r a c (m - 1) τ') := by
    intro t
    simp only [restTerm, hQt]
    rw [mul_add, mul_smul_comm, flagIntegral_add_smul]
    ring

  set R₀ : ℝ := ((restTerm f (r + a) Q₀ m τ (smallPowerSum f r a c (m - 1) τ') : ℚ) : ℝ)
  set K : ℝ := Real.log p * (2 * ((p : ℝ) ^ m)⁻¹)
  have hK : 0 < K := by
    have : 0 < Real.log p := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
    positivity
  have hslope : restTerm f (r + a) S m τ (smallPowerSum f r a c (m - 1) τ') = 0 := by
    by_contra hne
    set RS := restTerm f (r + a) S m τ (smallPowerSum f r a c (m - 1) τ')
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * Bnd / K + |R₀|)
    set t : ℚ := n / RS
    have h1 := hbd t e₁ he₁
    have h2 := hbd t e₂ he₂
    have hd := hdiff (Qt t)
    rw [hlin] at hd
    have htRS : t * RS = n := by simp only [t]; field_simp
    have hval : (((restTerm f (r + a) Q₀ m τ (smallPowerSum f r a c (m - 1) τ') +
        t * RS : ℚ)) : ℝ) = R₀ + n := by
      rw [htRS]; push_cast; rfl
    rw [hval] at hd
    have habs : |K * (R₀ + n)| ≤ 2 * Bnd := by
      rw [show K * (R₀ + n) = Real.log p * (2 * ((p : ℝ) ^ m)⁻¹ * (R₀ + n)) by ring, ← hd]
      calc _ ≤ |restPrimeModel f r a c (Qt t) s e₁ p| + |restPrimeModel f r a c (Qt t) s e₂ p| :=
            abs_sub _ _
        _ ≤ 2 * Bnd := by linarith
    rw [abs_mul, abs_of_pos hK] at habs
    have hR : (n : ℝ) - |R₀| ≤ |R₀ + n| := by
      have := abs_sub_abs_le_abs_sub (n : ℝ) (-R₀)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      have hn0 : |(n : ℝ)| = n := abs_of_nonneg (by positivity)
      linarith
    have : 2 * Bnd / K < n - |R₀| := by linarith
    have h3 : 2 * Bnd < K * (n - |R₀|) := by
      rw [div_lt_iff₀ hK] at this; linarith
    nlinarith
  simp only [restTerm] at hslope
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  exact (mul_eq_zero.1 hslope).resolve_left hm0

theorem flagIntegralReal_transfer_of_syzygy (f N j k : ℕ) (h : N = j + k) (F : RootRing f N)
    (Q₀ : ℕ → Fin f → RootRing f N) (hQ₀ : IsPowerSumDecomposition f N F Q₀)
    (Q' : Fin f → ℕ → IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hQ' : rootRingToReal f N j k h F =
      ∑ τ : Fin f, ∑ m ∈ Icc 1 (j + k), IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * Q' τ m)
    (m : ℕ) (τ : Fin f) (G : RootRing f N)
    (hS : ∀ S : ℕ → Fin f → RootRing f N, IsPowerSumDecomposition f N 0 S →
      flagIntegral f N (G * S m τ) = 0) :
    flagIntegralReal f (j + k) (rootRingToReal f N j k h G * Q' τ m) =
      (flagIntegral f N (G * Q₀ m τ) : ℝ) := by
  subst h
  have hid : (Prod.map id (finCongr (rfl : j + k = j + k)) : Fin f × Fin (j + k) → _) = id :=
    funext fun _ => rfl
  have hr : ∀ P : RootRing f (j + k), rootRingToReal f (j + k) j k rfl P = map (algebraMap ℚ ℝ) P :=
    fun P => by simp only [rootRingToReal, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, hid, rename_id_apply]
  have hp : ∀ m τ, IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ =
      map (algebraMap ℚ ℝ) (blockPowerSum f (j + k) m τ) := fun m τ => by
    rw [← hr, rootRingToReal_blockPowerSum]
  rw [hr] at hQ' ⊢
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℚ]
  intro φ
  have e1 := congrArg (TermBoundEq.coeffMap φ) hQ'
  simp only [TermBoundEq.coeffMap_map, TermBoundEq.coeffMap_sum, hp,
    TermBoundEq.coeffMap_map_mul] at e1
  have h0 : IsPowerSumDecomposition f (j + k) 0
      (fun m τ => TermBoundEq.coeffMap φ (Q' τ m) - φ 1 • Q₀ m τ) := by
    unfold IsPowerSumDecomposition at hQ₀ ⊢
    simp only [mul_sub, mul_smul_comm, sum_sub_distrib, ← smul_sum]
    rw [← hQ₀, sum_comm, ← e1, sub_self]
  have hT := hS _ h0
  rw [mul_sub, mul_smul_comm, TermBoundEq.flagIntegral_sub_smul] at hT
  have hc : φ ((flagIntegral f (j + k) (G * Q₀ m τ) : ℚ) : ℝ) =
      flagIntegral f (j + k) (G * Q₀ m τ) * φ 1 := by
    rw [← mul_one ((flagIntegral f (j + k) (G * Q₀ m τ) : ℚ) : ℝ), ← Rat.smul_def, map_smul,
      smul_eq_mul]
  rw [map_sub, TermBoundEq.dual_flagIntegralReal, TermBoundEq.coeffMap_map_mul, hc]
  linarith

end RestBoundEq

end

end GroundTheory.Heights₂.Heights.RestTerms
