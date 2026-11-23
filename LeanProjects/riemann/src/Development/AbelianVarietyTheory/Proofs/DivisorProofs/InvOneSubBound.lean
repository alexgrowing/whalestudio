import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
open NumberField IsDedekindDomain Polynomial GlobalTheory.HenQ

noncomputable section

namespace GlobalTheory.HenQ.Regroup

open IsDedekindDomain NumberField in
private lemma one_le_ramificationIdx_mul_inertiaDeg_of_mem (E : Type) [Field E]
    [NumberField E] (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {P : Ideal (NumberField.RingOfIntegers E)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (NumberField.RingOfIntegers E)) :
    1 ≤ p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P := by
  haveI := p.isMaximal
  rw [IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot] at hP
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver p.asIdeal := hP.2
  exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P p.ne_bot)
    (Ideal.inertiaDeg'_pos p.asIdeal P).ne')

open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.HenQ.Regroup.mem_fin (E : Type) [Field E] [NumberField E]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    v.asIdeal ∈
      IsDedekindDomain.primesOverFinset
        (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) v).asIdeal
        (NumberField.RingOfIntegers E) := by
  haveI := (HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) v).isMaximal
  rw [IsDedekindDomain.mem_primesOverFinset_iff
    (HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) v).ne_bot,
    HeightOneSpectrum.under_asIdeal]
  exact ⟨v.isPrime, inferInstance⟩

open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.HenQ.Regroup.term_pos (E : Type) [Field E] [NumberField E]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    (1 : ℕ) ≤
      (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) v).asIdeal.ramificationIdx'
          v.asIdeal *
        (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) v).asIdeal.inertiaDeg'
          v.asIdeal :=
  one_le_ramificationIdx_mul_inertiaDeg_of_mem E _ (_root_.GlobalTheory.HenQ.Regroup.mem_fin E v)

open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.HenQ.Regroup.sum_eq (E : Type) [Field E] [NumberField E]
    (hE : Module.finrank ℚ E = (2 : ℕ))
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (NumberField.RingOfIntegers E),
        p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P =
      (2 : ℕ) := by
  haveI := p.isMaximal
  rw [Ideal.sum_ramification_inertia (NumberField.RingOfIntegers E) ℚ E p.ne_bot, hE]

end GlobalTheory.HenQ.Regroup

namespace GlobalTheory.HenQ.Regroup

theorem exists_above (E : Type) [Field E] [NumberField E]
    (v : HeightOneSpectrum (𝓞 ℚ)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 ℚ) = v := by
  haveI := v.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hP.over, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 ℚ) (𝓞 E))
  refine ⟨⟨P, hPm.isPrime, hne⟩, ?_⟩
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact hP.over.symm

open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.HenQ.Regroup.two_le_absNorm {K : Type} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (2 : ℕ) ≤ (Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) p.asIdeal := by
  have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact p.ne_bot
  have h1 : Ideal.absNorm p.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact p.isPrime.ne_top
  omega

open IsDedekindDomain NumberField in
private lemma card_le_sum_ramificationIdx_mul_inertiaDeg_le_two (E : Type) [Field E]
    [NumberField E] (hE : Module.finrank ℚ E = 2)
    (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (T : Finset (Ideal (NumberField.RingOfIntegers E)))
    (hT : T ⊆ IsDedekindDomain.primesOverFinset p.asIdeal (NumberField.RingOfIntegers E)) :
    T.card ≤ ∑ P ∈ T, p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P ∧
      ∑ P ∈ T, p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P ≤ 2 := by
  constructor
  · rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun P hP =>
      one_le_ramificationIdx_mul_inertiaDeg_of_mem E p (hT hP)
  · calc ∑ P ∈ T, p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P
        ≤ ∑ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (NumberField.RingOfIntegers E),
            p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P :=
          Finset.sum_le_sum_of_subset hT
      _ = 2 := _root_.GlobalTheory.HenQ.Regroup.sum_eq E hE p

open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.HenQ.Regroup.fiber_split (E : Type) [Field E] [NumberField E]
    (hE : Module.finrank ℚ E = (2 : ℕ))
    (w w' v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hw' : IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) w' =
        IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) w)
    (hv : IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) v =
        IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) w)
    (hne : w' ≠ w) : v = w ∨ v = w' := by
  by_contra hcon
  push_neg at hcon
  have h1 : w.asIdeal ≠ w'.asIdeal := fun he => hne (HeightOneSpectrum.ext he).symm
  have h2 : w.asIdeal ≠ v.asIdeal := fun he => hcon.1 (HeightOneSpectrum.ext he).symm
  have h3 : w'.asIdeal ≠ v.asIdeal := fun he => hcon.2 (HeightOneSpectrum.ext he).symm
  have mw := _root_.GlobalTheory.HenQ.Regroup.mem_fin E w
  have mw' := _root_.GlobalTheory.HenQ.Regroup.mem_fin E w'
  have mv := _root_.GlobalTheory.HenQ.Regroup.mem_fin E v
  rw [hw'] at mw'
  rw [hv] at mv
  have hsub : ({w.asIdeal, w'.asIdeal, v.asIdeal} : Finset (Ideal (NumberField.RingOfIntegers E))) ⊆
      IsDedekindDomain.primesOverFinset
        (HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) w).asIdeal
        (NumberField.RingOfIntegers E) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl
    · exact mw
    · exact mw'
    · exact mv
  have hb := card_le_sum_ramificationIdx_mul_inertiaDeg_le_two E hE _ _ hsub
  have hcard :
      ({w.asIdeal, w'.asIdeal, v.asIdeal} : Finset (Ideal (NumberField.RingOfIntegers E))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3]
  omega

open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.HenQ.Regroup.fiber_inert (E : Type) [Field E] [NumberField E]
    (hE : Module.finrank ℚ E = (2 : ℕ))
    (w v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hN : (Ideal.absNorm : Ideal (NumberField.RingOfIntegers E) → ℕ) w.asIdeal =
        (Ideal.absNorm : Ideal (NumberField.RingOfIntegers ℚ) → ℕ)
            (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) w).asIdeal ^
          (2 : ℕ))
    (hv : IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) v =
        IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) w) :
    v = w := by
  by_contra hne
  have hne' : w.asIdeal ≠ v.asIdeal := fun he => hne (HeightOneSpectrum.ext he).symm
  have hw := _root_.GlobalTheory.HenQ.Regroup.mem_fin E w
  have hvm := _root_.GlobalTheory.HenQ.Regroup.mem_fin E v
  rw [hv] at hvm
  set p := HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) w with hp
  haveI : w.asIdeal.LiesOver p.asIdeal := by
    rw [hp, HeightOneSpectrum.under_asIdeal]
    infer_instance
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal p.asIdeal p.isPrime p.ne_bot
  rw [hN] at hn
  have hf : p.asIdeal.inertiaDeg' w.asIdeal = 2 :=
    (Nat.pow_right_injective (_root_.GlobalTheory.HenQ.Regroup.two_le_absNorm p) hn).symm
  have hwv := one_le_ramificationIdx_mul_inertiaDeg_of_mem E p hvm
  have hww := one_le_ramificationIdx_mul_inertiaDeg_of_mem E p hw
  have hsub : ({w.asIdeal, v.asIdeal} : Finset (Ideal (NumberField.RingOfIntegers E))) ⊆
      IsDedekindDomain.primesOverFinset p.asIdeal (NumberField.RingOfIntegers E) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact hw
    · exact hvm
  have hle := (card_le_sum_ramificationIdx_mul_inertiaDeg_le_two E hE p _ hsub).2
  rw [Finset.sum_pair hne', hf] at hle
  rw [hf] at hww
  omega

end GlobalTheory.HenQ.Regroup

namespace GlobalTheory.HenQ.Regroup

end GlobalTheory.HenQ.Regroup

namespace GlobalTheory.HenQ.Regroup

end GlobalTheory.HenQ.Regroup

namespace GlobalTheory.HenQ.Regroup

open IsDedekindDomain NumberField in
private lemma multipliable_of_norm_sub_one_le_summable {ι : Type*} (g : ι → ℂ) (u : ι → ℝ)
    (hu : Summable u) (hg : ∀ i, ‖g i - 1‖ ≤ u i) : Multipliable g := by
  have h := multipliable_one_add_of_summable (f := fun i => g i - 1)
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hg hu)
  simpa using h

open IsDedekindDomain NumberField in
private lemma norm_multiset_prod_sub_one_le (m : Multiset ℂ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hm : ∀ x ∈ m, ‖x - 1‖ ≤ ε) : ‖m.prod - 1‖ ≤ ε * (2 ^ Multiset.card m - 1) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha : ‖a - 1‖ ≤ ε := hm a (Multiset.mem_cons_self a m)
    have ih' := ih (fun x hx => hm x (Multiset.mem_cons_of_mem hx))
    have h2 : (1 : ℝ) ≤ 2 ^ Multiset.card m := one_le_pow₀ (by norm_num)
    have hP : ‖m.prod‖ ≤ 2 ^ Multiset.card m := by
      calc ‖m.prod‖ = ‖(m.prod - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ ‖m.prod - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ ε * (2 ^ Multiset.card m - 1) + 1 := by rw [norm_one]; linarith
        _ ≤ 2 ^ Multiset.card m := by
          nlinarith [mul_nonneg (sub_nonneg.2 hε1) (sub_nonneg.2 h2)]
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc ‖a * m.prod - 1‖ = ‖(a - 1) * m.prod + (m.prod - 1)‖ := by congr 1; ring
      _ ≤ ‖a - 1‖ * ‖m.prod‖ + ‖m.prod - 1‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ ε * 2 ^ Multiset.card m + ε * (2 ^ Multiset.card m - 1) :=
          add_le_add (mul_le_mul ha hP (norm_nonneg _) hε0) ih'
      _ = ε * (2 ^ Multiset.card m * 2 - 1) := by ring

open IsDedekindDomain NumberField in
private lemma norm_inv_one_sub_sub_one_le_two_mul {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 - z)⁻¹ - 1‖ ≤ 2 * ‖z‖ := by
  have h1 : (1 : ℝ) / 2 ≤ ‖1 - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at this
    linarith
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    norm_num at h1
  have hq : (1 - z)⁻¹ - 1 = z / (1 - z) := by
    rw [eq_div_iff hne, sub_mul, inv_mul_cancel₀ hne]
    ring
  rw [hq, norm_div, div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg z]

open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.HenQ.Regroup.multipliable_E (E : Type) [Field E] [NumberField E]
    (SE : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)))
    (BE : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E) → Multiset ℂ)
    (c₀ : ℝ) (r : ℕ)
    (hBE : ∀ w ∉ SE,
      (BE w).card ≤ r ∧
        ∀ b ∈ BE w,
          ‖b‖ ≤ (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers E) → ℕ) w.asIdeal) : ℝ) ^ c₀)
    (s : ℂ) (hs : c₀ + (1 : ℝ) < s.re) :
    Multipliable fun (w : { w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E) //
        w ∉ SE }) ↦
      (Multiset.map
          (fun (b : ℂ) ↦
            ((1 : ℂ) -
                b *
                  (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers E) → ℕ)
                          (↑w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)).asIdeal) :
                      ℂ) ^
                    (-s))⁻¹)
          (BE (↑w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)))).prod := by
  have hδ1 : 1 < s.re - c₀ := by linarith
  have hsum : Summable fun w : {w : HeightOneSpectrum (NumberField.RingOfIntegers E) // w ∉ SE} =>
      ((Ideal.absNorm (w : HeightOneSpectrum (NumberField.RingOfIntegers E)).asIdeal : ℕ) : ℝ) ^
        (-(s.re - c₀)) :=
    ((_root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow E).2 (s.re - c₀) hδ1).2.subtype _
  refine multipliable_of_norm_sub_one_le_summable _ _ (hsum.mul_left (2 * 2 ^ r)) (fun w => ?_)
  obtain ⟨hcard, hb⟩ := hBE w.1 w.2
  have hN2 : 2 ≤ Ideal.absNorm w.1.asIdeal := _root_.GlobalTheory.HenQ.Regroup.two_le_absNorm w.1
  set N : ℕ := Ideal.absNorm w.1.asIdeal with hN
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hsmall : (N : ℝ) ^ (-(s.re - c₀)) ≤ 1 / 2 := by
    calc (N : ℝ) ^ (-(s.re - c₀)) ≤ (N : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (N : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by
          rw [one_div]
          exact inv_anti₀ (by norm_num) hNR
  have hz : ∀ b ∈ BE w.1, ‖b * (N : ℂ) ^ (-s)‖ ≤ (N : ℝ) ^ (-(s.re - c₀)) := by
    intro b hbm
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    calc ‖b‖ * (N : ℝ) ^ (-s.re) ≤ (N : ℝ) ^ c₀ * (N : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hb b hbm) (by positivity)
      _ = (N : ℝ) ^ (-(s.re - c₀)) := by
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
  have hm := norm_multiset_prod_sub_one_le
    (Multiset.map (fun b => (1 - b * (N : ℂ) ^ (-s))⁻¹) (BE w.1))
    (ε := 2 * (N : ℝ) ^ (-(s.re - c₀))) (by positivity) (by linarith) (by
      intro x hx
      obtain ⟨b, hbm, rfl⟩ := Multiset.mem_map.mp hx
      have := hz b hbm
      exact (norm_inv_one_sub_sub_one_le_two_mul (by linarith)).trans (by linarith))
  rw [Multiset.card_map] at hm
  have hpow : (2 : ℝ) ^ (BE w.1).card ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hcard
  calc _ ≤ 2 * (N : ℝ) ^ (-(s.re - c₀)) * (2 ^ (BE w.1).card - 1) := hm
    _ ≤ 2 * (N : ℝ) ^ (-(s.re - c₀)) * 2 ^ r :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end GlobalTheory.HenQ.Regroup

namespace GlobalTheory.HenQ.Regroup

open IsDedekindDomain NumberField in
theorem _root_.GlobalTheory.HenQ.Regroup.fac_inert (B' : Multiset ℂ) (X : ℂ) :
    (Multiset.map (fun (b : ℂ) ↦ ((1 : ℂ) - b * X)⁻¹) (B' + Multiset.map Neg.neg B')).prod =
      (Multiset.map (fun (b : ℂ) ↦ ((1 : ℂ) - b * X ^ (2 : ℕ))⁻¹)
        (Multiset.map (fun (x : ℂ) ↦ x ^ (2 : ℕ)) B')).prod := by
  induction B' using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.cons_add, Multiset.prod_cons, Multiset.map_add,
      Multiset.prod_add] at ih ⊢
    rw [← ih]
    have hfac : ((1 : ℂ) - a ^ 2 * X ^ 2)⁻¹ = (1 - a * X)⁻¹ * (1 - -a * X)⁻¹ := by
      rw [← mul_inv]
      congr 1
      ring
    rw [hfac]
    ring

theorem core (E : Type) [Field E] [NumberField E] (hE : Module.finrank ℚ E = 2)
    (SQ : Set (HeightOneSpectrum (𝓞 ℚ))) (SE : Set (HeightOneSpectrum (𝓞 E)))
    (BQ : HeightOneSpectrum (𝓞 ℚ) → Multiset ℂ) (BE : HeightOneSpectrum (𝓞 E) → Multiset ℂ) (c₀ : ℝ) (r : ℕ)
    (hSE : ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 ℚ) ∈ SQ)
    (hBE : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE → Multiset.card (BE w) ≤ r ∧
      ∀ b ∈ BE w, ‖b‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀)
    (hloc : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE →
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 ℚ)).asIdeal ∧ ∃ w' : HeightOneSpectrum (𝓞 E), w' ≠ w ∧
        w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) ∧ BQ (w.under (𝓞 ℚ)) = BE w + BE w') ∨
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 ℚ)).asIdeal ^ 2 ∧ ∃ B' : Multiset ℂ,
        BE w = B'.map (· ^ 2) ∧ BQ (w.under (𝓞 ℚ)) = B' + B'.map Neg.neg))
    (s : ℂ) (hs : c₀ + 1 < s.re) : eulerL ℚ BQ SQ s = eulerL E BE SE s := by
  classical
  classical
  have hE' := (multipliable_E E SE BE c₀ r hBE s hs).hasProd
  let e : (Σ p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ},
      {w : HeightOneSpectrum (𝓞 E) // w.under (𝓞 ℚ) = p.1}) ≃ {w : HeightOneSpectrum (𝓞 E) // w ∉ SE} :=
    { toFun := fun x => ⟨x.2.1, by rw [hSE, x.2.2]; exact x.1.2⟩
      invFun := fun w => ⟨⟨w.1.under (𝓞 ℚ), (hSE w.1).not.mp w.2⟩, ⟨w.1, rfl⟩⟩
      left_inv := by rintro ⟨⟨p, hp⟩, ⟨w, hw⟩⟩; simp only at hw; subst hw; rfl
      right_inv := by intro w; rfl }
  have h2 := (e.hasProd_iff).mpr hE'
  refine (h2.sigma (g := fun p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ} =>
    ((BQ p.1).map fun b => (1 - b * ((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod) ?_).tprod_eq
  rintro ⟨p, hp⟩
  obtain ⟨w, rfl⟩ := exists_above E p
  have hwS : w ∉ SE := by rw [hSE]; exact hp
  rcases hloc w hwS with ⟨hN, w', hne, hw', hBQ⟩ | ⟨hN, B', hBE', hBQ⟩
  · have hN' : Ideal.absNorm w'.asIdeal = Ideal.absNorm (w.under (𝓞 ℚ)).asIdeal := by
      rcases hloc w' (by rw [hSE, hw']; exact hp) with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h, hw']
      · exact absurd (fiber_inert E hE w' w h hw'.symm) (Ne.symm hne)
    let a : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 ℚ) = w.under (𝓞 ℚ)} := ⟨w, rfl⟩
    let a' : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 ℚ) = w.under (𝓞 ℚ)} := ⟨w', hw'⟩
    have hall : ∀ c : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 ℚ) = w.under (𝓞 ℚ)}, c ∈ ({a, a'} : Finset _) := by
      intro c
      rcases fiber_split E hE w w' c.1 hw' c.2 hne with h | h
      · simp [Subtype.ext_iff, h, a]
      · simp [Subtype.ext_iff, h, a']
    have hne' : a ≠ a' := fun h => hne (congrArg Subtype.val h).symm
    convert hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (s := ({a, a'} : Finset _)) (fun c hc => absurd (hall c) hc) using 1
    rw [Finset.prod_pair hne']
    dsimp only [e, Equiv.coe_fn_mk, a, a', Function.comp_apply]
    rw [hBQ, Multiset.map_add, Multiset.prod_add, hN, hN']
  · let a : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 ℚ) = w.under (𝓞 ℚ)} := ⟨w, rfl⟩
    have hall : ∀ c : {v : HeightOneSpectrum (𝓞 E) // v.under (𝓞 ℚ) = w.under (𝓞 ℚ)}, c ∈ ({a} : Finset _) := by
      intro c
      have := fiber_inert E hE w c.1 hN c.2
      simp [Subtype.ext_iff, this, a]
    convert hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (s := ({a} : Finset _)) (fun c hc => absurd (hall c) hc) using 1
    rw [Finset.prod_singleton]
    dsimp only [e, Equiv.coe_fn_mk, a, Function.comp_apply]
    have hX : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) =
        (((Ideal.absNorm (w.under (𝓞 ℚ)).asIdeal : ℕ) : ℂ) ^ (-s)) ^ 2 := by
      rw [hN, pow_two, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, pow_two]
    rw [hX, hBE', hBQ, fac_inert]

end GlobalTheory.HenQ.Regroup
