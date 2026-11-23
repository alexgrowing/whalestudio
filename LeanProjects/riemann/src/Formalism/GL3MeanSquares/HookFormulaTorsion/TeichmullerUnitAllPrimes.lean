import Mathlib
import Formalism.GL3MeanSquares.ModelCocycleExponent

namespace Formalism.HermitianLattices.ModelCocycles

open Finset Formalism.HermitianLattices.IntegralLatticeDensity

theorem adjoint_from_norm : AdjointFromNorm := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hnm hlin α hα a b
  have h1 : ∀ a b', cob φ ((α : O) • a) ((α : O) • b') = nm α • cob φ a b' := by
    intro a b'; unfold cob; rw [← smul_add, hα, hα, hα, smul_sub, smul_sub]
  have h2 := h1 a ((↑α⁻¹ : O) • b)
  rw [smul_smul, Units.mul_inv, one_smul, ← hlin, hnm, smul_smul, mul_assoc, Units.mul_inv, mul_one] at h2
  exact h2

theorem adjoint_additive : AdjointAdd := by
  intro O M Q _ _ _ _ _ φ hadd α α' h h' a b
  have symm : ∀ a b, cob φ a b = cob φ b a := by
    intro a b; unfold cob; rw [add_comm a b]; abel
  rw [add_smul, hadd, h, h', star_add, add_smul, symm a (_ + _), hadd, symm a, symm a]

theorem cross_terms_vanish : CrossTermsVanish := by
  intro M N Q _ _ _ Φ hadd hneg x y
  have z : cob Φ ((0 : M), (0 : N)) (0, y) = 0 := by
    have := hadd ((0 : M), (0 : N)) (0, 0) (0, y); simpa using this
  have h1 : cob Φ (x, 0) (0, y) + cob Φ (-x, 0) (0, y) = 0 := by
    rw [← hadd]; simpa using z
  have h2 : cob Φ (-x, 0) (0, y) = cob Φ (x, 0) (0, y) := by
    unfold cob; simp [hneg]
  rw [h2] at h1; exact h1

theorem genus_one_character : GenusOneCharacter := by unfold GenusOneCharacter; decide

theorem split_component_vanishes : SplitVanish := by
  intro Z M Q _ _ _ _ _ φ a abar h1 h2 h3 hu hev h0 h22
  have symm : ∀ a b, cob φ a b = cob φ b a := by
    intro a b; unfold cob; rw [add_comm a b]; abel
  have c0 : ∀ x y, cob φ x y = 0 := by
    intro x y
    have e : (a - abar) • cob φ x y = 0 := by
      rw [sub_smul, ← h2, h3, symm x, h2, symm y, sub_self]
    obtain ⟨w, hw⟩ := hu
    have := congrArg (fun t => (↑w⁻¹ : Z) • t) e
    simpa [← hw, smul_smul] using this
  refine ⟨c0, fun u => h22 _ ?_⟩
  have := c0 u (-u)
  unfold cob at this
  rw [add_neg_cancel, h0, hev] at this
  have h : φ u + φ u = -(0 - φ u - φ u) := by abel
  rw [h, this, neg_zero]

theorem equal_powers_formula : EqualPowers := by
  intro R _ _ _ σ N f g hN hf hg h
  have hc := (Commute.all f g).mul_geom_sum₂ N
  rw [h, sub_self] at hc
  rcases mul_eq_zero.1 hc with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    have := congrArg MvPowerSeries.constantCoeff h1
    simp [map_sum, hf, hg] at this
    omega

theorem character_power_formula : ChiPower := by
  intro E _ _ Ψ A _ ι K χ hK hχ t h z k hk ht
  have e : χ t ^ h = χ (ι z) := by rw [← map_pow, ht, map_mul, hK k hk, mul_one]
  rw [← hχ, ← e, Circle.coe_pow]

theorem character_modulus_all : ChiModulusAll := by
  intro E _ _ Ψ A _ ι K χ hcm hK hχ t h z k hh hk ht s
  have e := character_power_formula E Ψ A ι K χ hK hχ t h z k hk ht
  have u : ∀ τ : E →+* ℂ, ‖s (τ (z : E))‖ = 1 := by
    intro τ
    have h1 : star (z : E) * (z : E) = 1 := (Unitary.mem_iff.1 z.2).1
    have h2 := congrArg (s.comp τ) h1
    rw [map_mul, map_one, hcm (s.comp τ)] at h2
    have h3 := congrArg (fun w : ℂ => ‖w‖) h2
    simp only [norm_mul, RCLike.norm_conj, norm_one, RingHom.comp_apply] at h3
    nlinarith [norm_nonneg (s (τ (z : E)))]
  have p : ‖s ((χ t : Circle) : ℂ)‖ ^ h = 1 := by
    rw [← norm_pow, ← map_pow, e, map_prod, norm_prod]
    apply Finset.prod_eq_one
    intro τ _
    rw [map_inv₀, norm_inv, u, inv_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hh.ne').1 p

theorem model_cocycle_exponent : ModelCocycleExponent := by
  intro E V _ _ _ _ h s hadd hherm hs x y a b ha hb hxy
  have hadd2 : ∀ x y y', h x (y + y') = h x y + h x y' := by
    intro x y y'; rw [hherm, hadd, star_add, ← hherm, ← hherm]
  have hyx : h y x = (a - b * s) / 2 := by
    rw [hherm y x, hxy, star_div₀, star_add, star_mul', ha, hb, hs, star_ofNat]; ring
  rw [hadd, hadd2, hadd2, hxy, hyx]; ring

theorem isotropic_vector_zero : IsotropicZero := by
  classical
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm hadd hadj hφ n ι _ _ f hiso t
  have symm : ∀ a b, cob φ a b = cob φ b a := by
    intro a b; unfold cob; rw [add_comm a b]; abel
  have hadd2 : ∀ a b b', cob φ a (b + b') = cob φ a b + cob φ a b' := by
    intro a b b'; rw [symm, hadd, symm b, symm b']
  have nm0 : nm 0 = 0 := hinj (by rw [hnm, map_zero, mul_zero])
  have φ0 : φ 0 = 0 := by
    have := hφ 0 0; rwa [zero_smul, nm0, zero_smul] at this
  let c : M → M →+ Q := fun a => AddMonoidHom.mk' (fun b => cob φ a b) (hadd2 a)
  have hc : ∀ a b, c a b = cob φ a b := fun _ _ => rfl
  have key : ∀ s : Finset ι, ∑ i, φ (∑ e ∈ s, f e i • t e) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [φ0]
    | insert a s ha ih =>
      have e1 : ∀ i, φ (∑ e ∈ insert a s, f e i • t e) =
          cob φ (f a i • t a) (∑ e ∈ s, f e i • t e) + φ (f a i • t a) + φ (∑ e ∈ s, f e i • t e) := by
        intro i; rw [Finset.sum_insert ha]; unfold cob; abel
      simp only [e1, Finset.sum_add_distrib, ih, add_zero]
      have e2 : ∑ i, φ (f a i • t a) = 0 := by
        simp only [hφ]
        rw [← Finset.sum_smul]
        have : ∑ i, nm (f a i) = 0 := hinj (by rw [map_sum, map_zero]; simp only [hnm]; exact hiso a a)
        rw [this, zero_smul]
      have e3 : ∑ i, cob φ (f a i • t a) (∑ e ∈ s, f e i • t e) = 0 := by
        have : ∀ i, cob φ (f a i • t a) (∑ e ∈ s, f e i • t e) =
            ∑ e ∈ s, c (t a) ((star (f a i) * f e i) • t e) := by
          intro i
          rw [hadj, ← hc, Finset.smul_sum, map_sum]
          simp only [smul_smul]
        simp only [this]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro e _
        rw [← map_sum, ← Finset.sum_smul, hiso, zero_smul, map_zero]
      rw [e2, e3, add_zero]
  simpa using key Finset.univ

theorem model_cocycle_order_two : ModelCocycleTwo := by
  intro d hd
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d + 1 = 8 * m := ⟨(d + 1) / 8, by omega⟩
  have n2 : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by have := Padic.norm_p (p := 2); simpa using this
  refine ⟨?_, ?_⟩
  · have n2' : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by have := PadicInt.norm_p (p := 2); simpa using this
    have H := hensels_lemma (p := 2) (R := ℤ_[2])
      (F := Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[2])) (a := 1) (by
        have e1 : Polynomial.aeval (1 : ℤ_[2]) (Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[2])) =
            2 ^ 3 * (m : ℤ_[2]) := by
          have : ((d + 1 : ℕ) : ℤ_[2]) = ((8 * m : ℕ) : ℤ_[2]) := by rw [hm]
          push_cast at this
          simp
          linear_combination this
        have e2 : Polynomial.aeval (1 : ℤ_[2])
            (Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[2]))) = 2 := by
          simp; norm_num
        rw [e1, e2, norm_mul, norm_pow, n2']
        have := PadicInt.norm_le_one (m : ℤ_[2])
        have h0 := norm_nonneg (m : ℤ_[2])
        nlinarith)
    obtain ⟨z, hz, _⟩ := H
    refine ⟨(z : ℚ_[2]), ?_⟩
    have hz' : z ^ 2 + (d : ℤ_[2]) = 0 := by simpa using hz
    have := congrArg (fun w : ℤ_[2] => (w : ℚ_[2])) hz'
    push_cast at this
    linear_combination this
  · intro δ hδ
    have nd : ‖(d : ℚ_[2])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff]
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
    have nδ : ‖δ‖ = 1 := by
      have : ‖δ‖ ^ 2 = 1 := by rw [← norm_pow, hδ, norm_neg, nd]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
    have δ0 : δ ≠ 0 := by intro h; rw [h, norm_zero] at nδ; exact zero_ne_one nδ
    let z : ℤ_[2] := ⟨δ, nδ.le⟩
    have hz : (z : ℚ_[2]) = δ := rfl
    have hz2 : z ^ 2 = -(d : ℤ_[2]) := by
      apply PadicInt.ext; push_cast; rw [hz, hδ]
    have hprod : (1 - z) * (1 + z) = 2 * (4 * (m : ℤ_[2])) := by
      have : ((d + 1 : ℕ) : ℤ_[2]) = ((8 * m : ℕ) : ℤ_[2]) := by rw [hm]
      push_cast at this
      linear_combination this - hz2
    have pr : Prime (2 : ℤ_[2]) := by have := PadicInt.prime_p (p := 2); simpa using this
    have both : (2 : ℤ_[2]) ∣ 1 - z ∧ (2 : ℤ_[2]) ∣ 1 + z := by
      rcases pr.dvd_or_dvd (Dvd.intro _ hprod.symm) with h | h
      · refine ⟨h, ?_⟩
        have : 1 + z = 2 - (1 - z) := by ring
        rw [this]; exact dvd_sub (dvd_refl _) h
      · refine ⟨?_, h⟩
        have : 1 - z = 2 - (1 + z) := by ring
        rw [this]; exact dvd_sub (dvd_refl _) h
    obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := both
    have hcq : 1 - δ = 2 * (c : ℚ_[2]) := by
      have := congrArg (fun w : ℤ_[2] => (w : ℚ_[2])) hc
      push_cast at this; rwa [hz] at this
    have hcq' : 1 + δ = 2 * (c' : ℚ_[2]) := by
      have := congrArg (fun w : ℤ_[2] => (w : ℚ_[2])) hc'
      push_cast at this; rwa [hz] at this
    refine ⟨?_, ?_, ?_⟩
    · rw [hcq, mul_div_mul_left _ _ two_ne_zero, norm_div, nδ, div_one]; exact c.2
    · rw [hcq', norm_div, norm_neg, ← norm_div, mul_div_mul_left _ _ two_ne_zero, norm_div, nδ, div_one]
      exact c'.2
    · intro a b
      field_simp
      ring

theorem jets_of_log_unit : JetsOfLogUnit := by
  intro K _ _ R U f hU hU0 hf n hn
  have hg : ∀ n, PowerSeries.coeff n (PowerSeries.derivative K f) ∈ R := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have h1 := congrArg (PowerSeries.coeff n) hf
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0,
        mul_one] at h1
      have hU' : PowerSeries.coeff n (PowerSeries.derivative K U) =
          PowerSeries.coeff (n + 1) U * ((n : K) + 1) := PowerSeries.coeff_derivative U n
      rw [hU'] at h1
      simp only [] at h1
      have h2 : PowerSeries.coeff n (PowerSeries.derivative K f) =
          PowerSeries.coeff (n + 1) U * ((n : K) + 1) -
            ∑ x ∈ range n, PowerSeries.coeff x (PowerSeries.derivative K f) *
              PowerSeries.coeff (n - x) U := by
        rw [← h1]; ring
      rw [h2]
      refine R.sub_mem (R.mul_mem (hU _) ?_) (R.sum_mem ?_)
      · exact_mod_cast natCast_mem R (n + 1)
      · intro x hx
        exact R.mul_mem (ih x (Finset.mem_range.1 hx)) (hU _)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h3 := hg k
  rw [PowerSeries.coeff_derivative] at h3
  have : ((k + 1).factorial : K) * PowerSeries.coeff (k + 1) f =
      (k.factorial : K) * (PowerSeries.coeff (k + 1) f * ((k : K) + 1)) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [this]
  exact R.mul_mem (natCast_mem R _) h3

private theorem witt_frobenius_sq_eq_neg (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (hp2 : p ≠ 2)
    (ε : WittVector p k) (hε : ε ^ (p ^ 2 - 1) = -1) :
    WittVector.frobenius (WittVector.frobenius ε) = -ε := by
  have hp := (Fact.out : p.Prime)
  set N := p ^ 2 - 1 with hN
  have hN1 : N + 1 = p ^ 2 := by
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hNe : Even N := by
    have : Odd (p ^ 2) := hodd.pow
    rw [← hN1] at this
    by_contra h
    rw [Nat.not_even_iff_odd] at h
    exact (Nat.not_even_iff_odd.2 this) (h.add_odd odd_one)
  set a := WittVector.frobenius (WittVector.frobenius ε) with ha
  set b := -ε with hb
  have haN : a ^ N = -1 := by rw [ha, ← map_pow, ← map_pow, hε, map_neg, map_neg, map_one, map_one]
  have hbN : b ^ N = -1 := by rw [hb, hNe.neg_pow, hε]
  have hc := (Commute.all a b).mul_geom_sum₂ N
  rw [haN, hbN, sub_self] at hc
  rcases mul_eq_zero.1 hc with h1 | h1
  · exact sub_eq_zero.1 h1
  · exfalso
    let c : WittVector p k →+* k := WittVector.constantCoeff
    have cfrob : ∀ x : WittVector p k, c (WittVector.frobenius x) = c x ^ p := fun x =>
      WittVector.coeff_frobenius_charP p x 0
    have cε : c ε ^ N = -1 := by rw [← map_pow, hε, map_neg, map_one]
    have cab : c a = c b := by
      rw [ha, hb, cfrob, cfrob, ← pow_mul, ← sq, ← hN1, pow_succ, cε, map_neg]; ring
    have cbN : c b ^ N = -1 := by rw [← map_pow, hbN, map_neg, map_one]
    have h2 := congrArg c h1
    rw [map_sum, map_zero] at h2
    have h3 : ∀ i ∈ range N, c (a ^ i * b ^ (N - 1 - i)) = c b ^ (N - 1) := by
      intro i hi
      have := Finset.mem_range.1 hi
      rw [map_mul, map_pow, map_pow, cab, ← pow_add]; congr 1; omega
    rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have hNk : (N : k) = -1 := by
      have : ((N + 1 : ℕ) : k) = 0 := by rw [hN1]; push_cast; simp
      push_cast at this
      linear_combination this
    have hb0 : c b ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by have := hp.two_le; nlinarith)] at cbN
      exact one_ne_zero (neg_eq_zero.1 cbN.symm)
    rw [hNk] at h2
    exact (mul_ne_zero (neg_ne_zero.2 one_ne_zero) (pow_ne_zero _ hb0)) h2

theorem teichmuller_unit_all_primes : EpsTeichAll := fun p _ hp2 ε hε => witt_frobenius_sq_eq_neg p _ hp2 ε hε

end Formalism.HermitianLattices.ModelCocycles
