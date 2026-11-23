import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

open Finset ArithmeticFunction

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem is_norm_one_iff : IsNormOneIff := by
  intro d N p
  have r1 : (1 : QuadraticAlgebra ℤ (-(((d + 1) / 4 : ℕ) : ℤ)) 1).re = 1 := rfl
  have i1 : (1 : QuadraticAlgebra ℤ (-(((d + 1) / 4 : ℕ) : ℤ)) 1).im = 0 := rfl
  constructor
  · rintro ⟨u, v, ⟨a, ha⟩, ⟨b, hb⟩, h⟩
    refine ⟨⟨u, v⟩, ⟨⟨a, b⟩, ?_⟩, ?_⟩
    · ext
      · simpa [r1] using ha
      · simpa [i1] using hb
    · rw [QuadraticAlgebra.norm_def, h]; ring
  · rintro ⟨π, ⟨w, hw⟩, h⟩
    have h1 := congrArg QuadraticAlgebra.re hw
    have h2 := congrArg QuadraticAlgebra.im hw
    refine ⟨π.re, π.im, ⟨w.re, by simpa [r1] using h1⟩, ⟨w.im, by simpa [i1] using h2⟩, ?_⟩
    rw [← h, QuadraticAlgebra.norm_def]; ring

theorem weighted_sum_identity : WGIdentity := by
  intro q _ χ a w M ha hw hM
  unfold Gchi
  have hsub : Icc 1 ⌊a / w⌋₊ ⊆ Icc 1 M := Icc_subset_Icc le_rfl hM
  rw [← Finset.sum_subset hsub (f := fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((max (a / n - w) 0 : ℝ) : ℂ))]
  · rw [mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      rw [mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hle : (n : ℝ) ≤ a / w := (Nat.le_floor_iff (by positivity)).1 hn.2
      have h1 : w ≤ a / n := by rw [le_div_iff₀ hn0]; rw [le_div_iff₀ hw] at hle; linarith
      rw [max_eq_left (by linarith)]
      have : w * (a / w / n - 1) = a / n - w := by field_simp
      rw [← this]; push_cast; ring
    · have : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
      push_cast; field_simp
  · intro n hn hn'
    rw [mem_Icc] at hn hn'
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have : a / w < n := by
      by_contra hc
      exact hn' ⟨hn.1, Nat.le_floor (not_lt.1 hc)⟩
    have h1 : a / n ≤ w := by rw [div_le_iff₀ hn0]; rw [div_lt_iff₀ hw] at this; linarith
    rw [max_eq_right (by linarith)]; simp

theorem finite_splitting_of_group : GFiniteSplit := by
  intro q _ χ x z hx hxz
  unfold Gchi Sz tailL cN
  have hsub : Icc 1 ⌊x⌋₊ ⊆ Icc 1 ⌊z⌋₊ := Icc_subset_Icc le_rfl (Nat.floor_le_floor hxz)
  have e1 : (∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - 1 : ℝ) : ℂ)) =
      ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - min 1 (x / n) : ℝ) : ℂ) := by
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [mem_Icc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have hle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).1 hn.2
      rw [min_eq_left ((one_le_div hn0).2 hle)]
    · intro n hn hn'
      rw [mem_Icc] at hn hn'
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      have : x < n := by
        by_contra hc
        exact hn' ⟨hn.1, Nat.le_floor (not_lt.1 hc)⟩
      rw [min_eq_right ((div_le_one hn0).2 this.le)]; simp
  rw [e1]
  have : ∀ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((x / n - min 1 (x / n) : ℝ) : ℂ) =
      (x : ℂ) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) - ((Λ n * min 1 (x / n) : ℝ) : ℂ) * χ (n : ZMod q) := by
    intro n _; push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem markov_discard_bound : MarkovDiscard := by
  intro P B J S V t ht hS hlt
  by_contra hcon
  push Not at hcon
  have hcov : P ⊆ B ∪ (Finset.univ.biUnion fun j => P.filter fun q => t < |S j q|) := by
    intro q hq
    by_cases hB : q ∈ B
    · exact mem_union_left _ hB
    · obtain ⟨j, hj⟩ := hcon q hq hB
      exact mem_union_right _ (mem_biUnion.2 ⟨j, mem_univ _, mem_filter.2 ⟨hq, hj⟩⟩)
  have hj : ∀ j, (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) ≤ V / t ^ 2 * P.card := by
    intro j
    have h1 : (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) * t ^ 2 ≤ ∑ q ∈ P, S j q ^ 2 := by
      calc (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) * t ^ 2
          = ∑ q ∈ P.filter (fun q => t < |S j q|), t ^ 2 := by simp
        _ ≤ ∑ q ∈ P.filter (fun q => t < |S j q|), S j q ^ 2 := by
            apply Finset.sum_le_sum
            intro q hq
            have := (mem_filter.1 hq).2
            rw [← sq_abs (S j q)]
            exact pow_le_pow_left₀ ht.le this.le 2
        _ ≤ ∑ q ∈ P, S j q ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    have h2 := h1.trans (hS j)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact h2
  have hc : (P.card : ℝ) ≤ B.card + ∑ j : Fin J, (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) := by
    have := (Finset.card_le_card hcov).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
    exact_mod_cast this
  have : ∑ j : Fin J, (((P.filter fun q => t < |S j q|).card : ℕ) : ℝ) ≤ J * (V / t ^ 2 * P.card) := by
    calc _ ≤ ∑ _j : Fin J, V / t ^ 2 * P.card := Finset.sum_le_sum fun j _ => hj j
      _ = _ := by simp
  nlinarith

theorem norm_one_congruence : NormOneCongr := by
  intro d N p h
  have key : ((p : ℤ) ≡ 1 [ZMOD (N : ℤ)]) := by
    obtain ⟨u, v, ⟨a, ha⟩, ⟨b, hb⟩, h⟩ := h
    have hu : u = 1 + N * a := by linarith
    rw [h, hu, hb]
    apply Int.modEq_iff_dvd.2
    refine ⟨-(2 * a + N * a ^ 2 + b + N * a * b + (((d + 1) / 4 : ℕ) : ℤ) * N * b ^ 2), ?_⟩
    ring
  refine ⟨key, fun χ => ?_⟩
  have : ((p : ℕ) : ZMod N) = 1 := by
    have := (ZMod.intCast_eq_intCast_iff (p : ℤ) 1 N).2 key
    simpa using this
  rw [this, map_one]

theorem class_splits : ClassSplit := by
  intro y q₁ d hq hd hM
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have main : ∀ p : ℕ, p.Prime → p ∣ (d + 1) / 4 → SplitsIn d p := by
    intro p hp hdiv
    have := Fact.mk hp
    refine ⟨0, 1, zero_ne_one, ?_, ?_⟩ <;> simp [(ZMod.natCast_eq_zero_iff _ _).2 hdiv]
  have odd : ∀ p : ℕ, p.Prime → p ∣ d + 1 → p ∣ (d + 1) / 4 := by
    intro p hp hdiv
    by_cases h2 : p = 2
    · subst h2; omega
    · rw [← h4] at hdiv
      rcases (Nat.Prime.dvd_mul hp).1 hdiv with h | h
      · exfalso
        have : p ∣ 2 ^ 2 := by simpa using h
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this))
      · exact h
  refine ⟨main _ hq (odd _ hq ((Dvd.intro _ rfl).trans hM)), fun p hp hpy => ?_⟩
  by_cases h2 : p = 2
  · subst h2; exact main 2 hp (by omega)
  · apply main _ hp (odd _ hp _)
    refine Dvd.dvd.trans ?_ hM
    apply Dvd.dvd.mul_left
    apply Finset.dvd_prod_of_mem (fun p => p)
    simp only [mem_filter, mem_Icc]
    refine ⟨⟨?_, Nat.le_floor hpy⟩, hp⟩
    have := hp.two_le; omega

theorem primorial_upper_bound : PrimorialBound := by
  intro y q₁ hy hq
  unfold oddM
  have h1 : (∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p) ≤ primorial ⌊y⌋₊ := by
    unfold primorial
    apply Finset.prod_le_prod_of_subset_of_one_le'
    · intro p hp
      simp only [mem_filter, mem_Icc, mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p hp _
      exact (mem_filter.1 hp).2.one_lt.le
  have h2 : ((∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ) ≤ Real.exp (2 * y) := by
    calc ((∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ) ≤ ((4 ^ ⌊y⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast h1.trans (primorial_le_four_pow _)
      _ = (4 : ℝ) ^ (⌊y⌋₊ : ℝ) := by push_cast; rw [Real.rpow_natCast]
      _ ≤ (4 : ℝ) ^ y := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hy)
      _ = Real.exp (Real.log 4 * y) := by rw [Real.rpow_def_of_pos (by norm_num)]
      _ ≤ Real.exp (2 * y) := by
          apply Real.exp_le_exp.2
          have : Real.log 4 ≤ 2 := by
            have : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
            have := Real.log_two_lt_d9
            linarith
          nlinarith
  calc ((q₁ * ∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ)
      = (q₁ : ℝ) * ((∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ) := by push_cast; ring
    _ ≤ Real.exp y * Real.exp (2 * y) := mul_le_mul hq h2 (by positivity) (by positivity)
    _ = Real.exp (3 * y) := by rw [← Real.exp_add]; ring_nf

theorem weighted_sum_lipschitz : WGLipschitz := by
  intro q _ χ a w w' ha hw hww
  have hw' : 0 < w' := lt_of_lt_of_le hw hww
  have hW : WGIdentity := weighted_sum_identity
  have hfl : ⌊a / w'⌋₊ ≤ ⌊a / w⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_left ha.le hw hww)
  rw [hW q χ a w' ⌊a / w⌋₊ ha hw' hfl, hW q χ a w ⌊a / w⌋₊ ha hw le_rfl]
  rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  have hpsi : Chebyshev.psi (a / w) = ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n := by
    unfold Chebyshev.psi; rfl
  rw [hpsi, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [← mul_sub, norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg vonMangoldt_nonneg]
  have h1 : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have h2 : ‖max (a / n - w') 0 - max (a / n - w) 0‖ ≤ w' - w := by
    have := abs_max_sub_max_le_abs (a / n - w') (a / n - w) 0
    rw [Real.norm_eq_abs]
    refine this.trans ?_
    rw [show a / n - w' - (a / n - w) = -(w' - w) by ring, abs_neg, abs_of_nonneg (by linarith)]
  calc Λ n * ‖χ (n : ZMod q)‖ * ‖max (a / n - w') 0 - max (a / n - w) 0‖
      ≤ Λ n * 1 * (w' - w) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 vonMangoldt_nonneg) h2 (norm_nonneg _)
        simp
    _ = Λ n * (w' - w) := by ring

theorem type_sign_formula : TypeSign := by
  intro q₁ d _ _ h1 h2 hdvd
  have o1 : Odd q₁ := Nat.odd_iff.2 (by omega)
  have o2 : Odd d := Nat.odd_iff.2 (by omega)
  have h : jacobiSym (-(d : ℤ)) q₁ = 1 := by
    have : (-(d : ℤ)) % (q₁ : ℤ) = 1 % (q₁ : ℤ) := by
      apply Int.modEq_iff_dvd.2
      have : ((q₁ : ℕ) : ℤ) ∣ ((d + 1 : ℕ) : ℤ) := by exact_mod_cast hdvd
      convert this using 1
      push_cast; ring
    rw [jacobiSym.mod_left' this, jacobiSym.one_left]
  refine ⟨h, ?_⟩
  rw [jacobiSym.neg _ o1, ZMod.χ₄_nat_three_mod_four (by omega)] at h
  rw [jacobiSym.neg _ o2, ZMod.χ₄_nat_three_mod_four (by omega),
    jacobiSym.quadratic_reciprocity_three_mod_four (by omega) (by omega)]
  linarith

theorem weighted_von_mangoldt_sum_identity (a w : ℝ) (M : ℕ) (ha : 0 < a) (hw : 0 < w) (hM : ⌊a / w⌋₊ ≤ M) :
    w * (∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * (a / w / n - 1)) = ∑ n ∈ Icc 1 M, Λ n * max (a / n - w) 0 := by
  have hsub : Icc 1 ⌊a / w⌋₊ ⊆ Icc 1 M := Icc_subset_Icc le_rfl hM
  rw [← Finset.sum_subset hsub (f := fun n => Λ n * max (a / n - w) 0), Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hle : (n : ℝ) ≤ a / w := (Nat.le_floor_iff (by positivity)).1 hn.2
    have h1 : w ≤ a / n := by rw [le_div_iff₀ hn0]; rw [le_div_iff₀ hw] at hle; linarith
    rw [max_eq_left (by linarith)]
    have : w * (a / w / n - 1) = a / n - w := by field_simp
    rw [← this]; ring
  · intro n hn hn'
    rw [mem_Icc] at hn hn'
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have : a / w < n := by
      by_contra hc
      exact hn' ⟨hn.1, Nat.le_floor (not_lt.1 hc)⟩
    have h1 : a / n ≤ w := by rw [div_le_iff₀ hn0]; rw [div_lt_iff₀ hw] at this; linarith
    rw [max_eq_right (by linarith)]; simp

theorem weight_one_sum_lipschitz : WeightedSumLipschitzTrivial := by
  intro a w w' ha hw hww
  have hw' : 0 < w' := lt_of_lt_of_le hw hww
  have hfl : ⌊a / w'⌋₊ ≤ ⌊a / w⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_left ha.le hw hww)
  unfold G1
  have e1 := weighted_von_mangoldt_sum_identity a w' ⌊a / w⌋₊ ha hw' hfl
  have e2 := weighted_von_mangoldt_sum_identity a w ⌊a / w⌋₊ ha hw le_rfl
  have hpsi : Chebyshev.psi (a / w) = ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n := by
    unfold Chebyshev.psi; rfl
  have hS : |(∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * max (a / n - w') 0) - ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * max (a / n - w) 0|
      ≤ Chebyshev.psi (a / w) * (w' - w) := by
    rw [← Finset.sum_sub_distrib, hpsi, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [← mul_sub, abs_mul, abs_of_nonneg vonMangoldt_nonneg]
    apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
    refine (abs_max_sub_max_le_abs (a / n - w') (a / n - w) 0).trans ?_
    rw [show a / n - w' - (a / n - w) = -(w' - w) by ring, abs_neg, abs_of_nonneg (by linarith)]
  have hlog : |a * (Real.log (a / w) - Real.log (a / w'))| ≤ a / w * (w' - w) := by
    rw [Real.log_div ha.ne' hw.ne', Real.log_div ha.ne' hw'.ne']
    have h0 : 0 ≤ Real.log w' - Real.log w := sub_nonneg.2 (Real.log_le_log hw hww)
    have h1 : Real.log w' - Real.log w ≤ (w' - w) / w := by
      rw [← Real.log_div hw'.ne' hw.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hw' hw)
      have e : w' / w - 1 = (w' - w) / w := by field_simp
      linarith
    rw [show Real.log a - Real.log w - (Real.log a - Real.log w') = Real.log w' - Real.log w by ring,
      abs_of_nonneg (mul_nonneg ha.le h0)]
    calc a * (Real.log w' - Real.log w) ≤ a * ((w' - w) / w) := mul_le_mul_of_nonneg_left h1 ha.le
      _ = a / w * (w' - w) := by ring
  have hmain : w' * ((∑ n ∈ Icc 1 ⌊a / w'⌋₊, Λ n * (a / w' / n - 1)) - a / w' * (Real.log (a / w') - 1 - Real.eulerMascheroniConstant))
      - w * ((∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * (a / w / n - 1)) - a / w * (Real.log (a / w) - 1 - Real.eulerMascheroniConstant))
      = ((∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * max (a / n - w') 0) - ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * max (a / n - w) 0)
        + a * (Real.log (a / w) - Real.log (a / w')) := by
    rw [← e1, ← e2]; field_simp; ring
  rw [hmain, add_mul]
  exact (abs_add_le _ _).trans (add_le_add hS hlog)

theorem class_admissible : ClassAdmissible := by
  intro y z q₁ hy hq h8 hz
  set M := oddM y q₁ with hMdef
  have hMpf : ∀ p : ℕ, p.Prime → p ∣ M → p = q₁ ∨ (3 ≤ p ∧ (p : ℝ) ≤ y) := by
    intro p hp hdiv
    rcases (Nat.Prime.dvd_mul hp).1 hdiv with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
    · obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
      simp only [mem_filter, mem_Icc] at hr
      have : p = r := (Nat.prime_dvd_prime_iff_eq hp hr.2).1 hpr
      subst this
      exact Or.inr ⟨hr.1.1, (Nat.le_floor_iff (by linarith)).1 hr.1.2⟩
  have hMpos : 0 < M := by
    apply Nat.mul_pos hq.pos
    exact Finset.prod_pos fun p hp => (mem_filter.1 hp).2.pos
  have hcop : Nat.Coprime 16 M := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h
    rcases hMpf 2 Nat.prime_two h with h | h
    · omega
    · omega
  obtain ⟨a₀, h16, hM⟩ := Nat.chineseRemainder hcop 7 (M - 1)
  have h16' : a₀ % 16 = 7 := h16
  have hM' : M ∣ a₀ + 1 := by
    have : a₀ + 1 ≡ (M - 1) + 1 [MOD M] := Nat.ModEq.add_right 1 hM
    rw [Nat.sub_add_cancel hMpos] at this
    exact (Nat.modEq_zero_iff_dvd).1 (this.trans (by simp [Nat.ModEq]))
  have hcM : a₀.Coprime M := by
    have : Nat.Coprime a₀ (a₀ + 1) := by simp
    exact Nat.Coprime.coprime_dvd_right hM' this
  have hc16 : a₀.Coprime 16 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  refine ⟨a₀, h16', hM', Nat.Coprime.mul_right hc16 hcM, by omega, Dvd.dvd.mul_right (by norm_num) _, ?_, ?_⟩
  · intro p hp hdiv
    rcases (Nat.Prime.dvd_mul hp).1 hdiv with h | h
    · have : p ∣ 2 ^ 4 := by simpa using h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)
      subst this; left; exact_mod_cast hy
    · rcases hMpf p hp h with h | h
      · subst h; exact Or.inr hz
      · exact Or.inl h.2
  · intro d hd
    have hd' : d ≡ a₀ [MOD 16 * M] := hd
    have d16 : d ≡ a₀ [MOD 16] := Nat.ModEq.of_mul_right M hd'
    have dM : d ≡ a₀ [MOD M] := Nat.ModEq.of_mul_left 16 hd'
    refine ⟨d16.trans h16, ?_⟩
    exact (Nat.modEq_zero_iff_dvd).1 ((Nat.ModEq.add_right 1 dM).trans ((Nat.modEq_zero_iff_dvd).2 hM'))

theorem character_sum_of_hypothesis : CharacterSumLipschitzOfChebyshev := by
  intro hpsi
  refine ⟨fun q _ χ a w w' ha hw hww => ?_, fun a w w' ha hw hww => ?_⟩
  · refine (weighted_sum_lipschitz q χ a w w' ha hw hww).trans ?_
    have h1 := hpsi (a / w) (by positivity)
    have h2 : 0 ≤ a / w := by positivity
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    rw [mul_div_assoc]; linarith
  · refine (weight_one_sum_lipschitz a w w' ha hw hww).trans ?_
    have h1 := hpsi (a / w) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    rw [mul_div_assoc]; linarith

theorem twist_evaluation_formula : TwEval := by
  intro t θ q _ n
  by_cases hu : IsUnit (n : ZMod (t * q))
  · unfold tw
    rw [MulChar.mul_apply]
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu']
    have h1 : (ZMod.cast ((n : ZMod (t * q))) : ZMod t) = (n : ZMod t) := by
      have : (ZMod.castHom (Dvd.intro q rfl : t ∣ t * q) (ZMod t)) (n : ZMod (t*q)) = (n : ZMod t) := map_natCast _ n
      simpa using this
    have h2 : (ZMod.cast ((n : ZMod (t * q))) : ZMod q) = (n : ZMod q) := by
      have : (ZMod.castHom (Dvd.intro_left t rfl : q ∣ t * q) (ZMod q)) (n : ZMod (t*q)) = (n : ZMod q) := map_natCast _ n
      simpa using this
    rw [h1, h2]
    congr 1
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    simp [qc, legendreSym]
  · rw [MulChar.map_nonunit _ hu]
    have hc : ¬ n.Coprime (t * q) := fun h => hu ((ZMod.isUnit_iff_coprime n _).2 h)
    by_cases h1 : n.Coprime t
    · have h2 : ¬ n.Coprime q := fun h => hc (Nat.Coprime.mul_right h1 h)
      have : jacobiSym (n : ℤ) q = 0 := by
        have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
        rw [jacobiSym.eq_zero_iff_not_coprime]
        simpa [Int.gcd_natCast_natCast] using h2
      simp [this]
    · have : θ (n : ZMod t) = 0 := MulChar.map_nonunit _ (fun h => h1 ((ZMod.isUnit_iff_coprime n _).1 h))
      simp [this]

theorem splits_iff_jacobi_symbol : SplitsIffJacobi := by
  intro d p hp hd
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  refine ⟨fun hp2 => ?_, ?_⟩
  · have := Fact.mk hp
    have h4' : (4 : ZMod p) * (((d + 1) / 4 : ℕ) : ZMod p) = (d : ZMod p) + 1 := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) h4
    have two : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    have four : (4 : ZMod p) ≠ 0 := by
      have : (4 : ZMod p) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero two two
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    have cast : (((-(d : ℤ)) : ℤ) : ZMod p) = -(d : ZMod p) := by push_cast; rfl
    unfold SplitsIn
    constructor
    · rintro ⟨r, s, hrs, hr, hs⟩
      have sqr : (2 * r - 1) * (2 * r - 1) = -(d : ZMod p) := by linear_combination 4 * hr - h4'
      have sqs : (2 * s - 1) * (2 * s - 1) = -(d : ZMod p) := by linear_combination 4 * hs - h4'
      have hne : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
        rw [cast]; intro h0
        rw [h0] at sqr sqs
        have a := mul_self_eq_zero.1 sqr
        have b := mul_self_eq_zero.1 sqs
        apply hrs
        have : 2 * (r - s) = 0 := by linear_combination a - b
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h two
        · exact sub_eq_zero.1 h
      rw [legendreSym.eq_one_iff p hne, cast]
      exact ⟨2 * r - 1, sqr.symm⟩
    · intro h
      have hne : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
        intro h0
        rw [(legendreSym.eq_zero_iff p _).2 h0] at h; exact absurd h (by norm_num)
      obtain ⟨t, ht⟩ := (legendreSym.eq_one_iff p hne).1 h
      rw [cast] at ht hne
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hne (by simpa using ht)
      have hr2 : 2 * ((1 + t) / 2) = 1 + t := by field_simp
      have hs2 : 2 * ((1 - t) / 2) = 1 - t := by field_simp
      refine ⟨(1 + t) / 2, (1 - t) / 2, ?_, ?_, ?_⟩
      · intro he
        have e : 1 + t = 1 - t := by rw [← hr2, ← hs2, he]
        have : 2 * t = 0 := by linear_combination e
        rcases mul_eq_zero.1 this with h | h
        · exact two h
        · exact ht0 h
      · apply (mul_eq_zero.1 (?_ : (4 : ZMod p) * _ = 0)).resolve_left four
        linear_combination (2 * ((1 + t) / 2) + t - 1) * hr2 + h4' - ht
      · apply (mul_eq_zero.1 (?_ : (4 : ZMod p) * _ = 0)).resolve_left four
        linear_combination (2 * ((1 - t) / 2) - t - 1) * hs2 + h4' - ht
  · unfold SplitsIn
    constructor
    · rintro ⟨r, -, -, hr, -⟩
      by_contra h
      have hodd : ((d + 1) / 4) % 2 = 1 := by omega
      have : (((d + 1) / 4 : ℕ) : ZMod 2) = 1 := by
        rw [← ZMod.natCast_mod, hodd]; rfl
      rw [this] at hr
      revert hr; revert r; decide
    · intro h
      have : (((d + 1) / 4 : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 (by omega)
      exact ⟨0, 1, by decide, by simp [this], by simp [this]⟩

theorem exponential_sum_split : ExpSplit := by
  intro c v lam hc hv hl
  have hs := Real.sqrt_nonneg v
  have hsq : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv
  rcases le_total (Real.sqrt v) lam with h | h
  · have : Real.exp (-c * v / (lam + Real.sqrt v)) ≤ Real.exp (-c * v / (2 * lam)) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hc.le hv, mul_nonneg (mul_nonneg hc.le hv) (sub_nonneg.mpr h)]
    linarith [Real.exp_pos (-c * Real.sqrt v / 2)]
  · have : Real.exp (-c * v / (lam + Real.sqrt v)) ≤ Real.exp (-c * Real.sqrt v / 2) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hc.le hs, mul_nonneg (mul_nonneg hc.le hs) (sub_nonneg.mpr h)]
    linarith [Real.exp_pos (-c * v / (2 * lam))]

theorem no_exceptional_zero_of_box_count : NoExcOfBox := by
  intro c₁ Q q _ χ hQ hc hbox hreal
  refine ⟨by simp, by simp, ?_⟩
  intro s hs hz
  exfalso
  have him := hreal s hs hz
  have h1 : 1 - c₁ / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hs
  rw [him] at h1
  have h2 : (q : ℝ) * (|(0:ℝ)| + 2) = 2 * q := by simp; ring
  rw [h2] at h1
  exact hbox s (by linarith) (by rw [him]; simpa using hQ) hz.2

theorem type_sign_of_split : TypeSignOfSplit := by
  intro q₁ d h1 h2 h
  have o1 : Odd q₁ := Nat.odd_iff.2 (by omega)
  have o2 : Odd d := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.neg _ o1, ZMod.χ₄_nat_three_mod_four h1] at h
  rw [jacobiSym.neg _ o2, ZMod.χ₄_nat_three_mod_four h2, jacobiSym.quadratic_reciprocity_three_mod_four h1 h2]
  linarith

end Formalism.HermitianLattices.ZeroFreeRegionGL2
