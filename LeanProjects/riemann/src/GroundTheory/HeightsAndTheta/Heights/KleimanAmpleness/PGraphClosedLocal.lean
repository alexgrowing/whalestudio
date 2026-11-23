import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GeneratedTwistSysZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace GraphClosedAlt

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem chartRing_subset_ampleChart (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a : Ω}
    (ha : a ∈ chartRing S x I) : a ∈ ampleChart H 1 h I := by
  refine ⟨0, ?_⟩
  rw [pow_zero, mul_one, mul_zero]
  change a ∈ twistMod S x 0 I
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero]
  have : a = (⟨a, ha⟩ : chartRing S x I) • (1 : Ω) := by rw [chartRing_smul_def, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem ampleChart_mul (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a b : Ω}
    (ha : a ∈ ampleChart H 1 h I) (hb : b ∈ ampleChart H 1 h I) : a * b ∈ ampleChart H 1 h I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  rw [one_mul] at hn hm ⊢
  rw [SubSystem.pow_sub] at hn hm ⊢
  rw [pow_add, pow_add]
  have : a * b * (h ^ n * h ^ m) = (a * h ^ n) * (b * h ^ m) := by ring
  rw [this]
  exact Submodule.mul_mem_mul hn hm

theorem ampleChart_pow (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a : Ω}
    (ha : a ∈ ampleChart H 1 h I) (e : ℕ) : a ^ e ∈ ampleChart H 1 h I := by
  induction e with
  | zero => rw [pow_zero]; exact chartRing_subset_ampleChart H h I (one_mem _)
  | succ e ih => rw [pow_succ]; exact ampleChart_mul H h I ih ha

def chartUnion (I J : Chart x) : Chart x :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩

theorem xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

theorem div_mem_chartRing (I : Chart x) (j : Fin (N + 1)) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    x j / x i ∈ chartRing S x I :=
  ⟨X j, X i, 1, X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩

theorem exists_pow_mul_ratio_mem (I J : Chart x) {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I.1)
    {i : Fin (N + 1)} (hi : i ∈ I.1 ∪ J.1) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * (x i₀ / x i) ∈ chartRing S x I := by
  by_cases hiI : i ∈ I.1
  · exact ⟨0, by rw [pow_zero, one_mul]; exact div_mem_chartRing I i₀ hiI⟩
  have hiJ : i ∈ J.1 := (Finset.mem_union.mp hi).resolve_left hiI
  refine ⟨1, ?_⟩
  have hw : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  have hxi : x i ≠ 0 := (mem_support x).mp (J.2.2 hiJ)
  have hQ : xProd I ≠ 0 := xProd_ne_zero I
  obtain ⟨m, hm⟩ : ∃ m, I.1.card = m + 1 := ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  obtain ⟨c, hc⟩ : ∃ c, J.1.card = c + 1 := ⟨J.1.card - 1, (Nat.succ_pred_eq_of_pos J.2.1.card_pos).symm⟩
  have hce : (J.1.erase i).card = c := by rw [Finset.card_erase_of_mem hiJ, hc]; rfl
  set P := ∏ j ∈ J.1.erase i, x j with hP
  have hJP : xProd J = x i * P := (Finset.mul_prod_erase J.1 x hiJ).symm
  have hprodI : ∏ i' ∈ I.1, (x i₀ / x i') = x i₀ ^ (m + 1) / xProd I := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hm]; rfl
  have hprodJ : ∏ j ∈ J.1.erase i, (x j / x i₀) = P / x i₀ ^ c := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hce]
  have key : (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ 1 * (x i₀ / x i) =
      (x i / x i₀) ^ m * (∏ j ∈ J.1.erase i, (x j / x i₀)) ^ (m + 1) *
        (∏ i' ∈ I.1, (x i₀ / x i')) ^ (c + 1) := by
    rw [hprodI, hprodJ, hJP, hm, hc, pow_one]
    simp only [div_pow, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [key]
  refine mul_mem (mul_mem (pow_mem (div_mem_chartRing I i hi₀) m)
    (pow_mem (prod_mem fun j _ => div_mem_chartRing I j hi₀) _))
    (pow_mem (prod_mem fun i' hi' => div_mem_chartRing I i₀ hi') _)

theorem exists_pow_mul_mem_chartRing (I J : Chart x) {z : Ω}
    (hz : z ∈ chartRing S x (chartUnion I J)) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * z ∈ chartRing S x I := by
  set σ := xProd J ^ I.1.card / xProd I ^ J.1.card
  obtain ⟨i₀, hi₀⟩ := I.2.1
  have hw : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  have hmon : ∀ s ∈ monos (S := S) (I.1 ∪ J.1), ∃ (e d : ℕ), s.IsHomogeneous d ∧
      σ ^ e * (x i₀ ^ d / aeval x s) ∈ chartRing S x I := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem a ha =>
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨e, he⟩ := exists_pow_mul_ratio_mem (S := S) I J hi₀ (i := i) (by exact_mod_cast hi)
      exact ⟨e, 1, isHomogeneous_X S i, by rw [pow_one, aeval_X]; exact he⟩
    | one => exact ⟨0, 0, isHomogeneous_one _ _, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨e₁, d₁, had, hae⟩ := ha
      obtain ⟨e₂, d₂, hbd, hbe⟩ := hb
      refine ⟨e₁ + e₂, d₁ + d₂, had.mul hbd, ?_⟩
      have : σ ^ (e₁ + e₂) * (x i₀ ^ (d₁ + d₂) / aeval x (a * b)) =
          (σ ^ e₁ * (x i₀ ^ d₁ / aeval x a)) * (σ ^ e₂ * (x i₀ ^ d₂ / aeval x b)) := by
        rw [map_mul, pow_add, pow_add]; ring
      rw [this]
      exact mul_mem hae hbe
  obtain ⟨f, s, d, hs, hf, hsd, rfl⟩ := hz
  obtain ⟨e, d', hsd', hmem⟩ := hmon s hs
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (chartUnion I J) hs
  have hsne : s ≠ 0 := fun h => hs0 (by rw [h, map_zero])
  have hdd : d' = d := hsd'.inj_right hsd hsne
  subst hdd
  have hf' : aeval x f / x i₀ ^ d' ∈ chartRing S x I :=
    ⟨f, X i₀ ^ d', d', pow_mem (X_mem_monos hi₀) d', hf, isHomogeneous_X_pow i₀ d', by simp⟩
  refine ⟨e, ?_⟩
  have : σ ^ e * (aeval x f / aeval x s) = (aeval x f / x i₀ ^ d') * (σ ^ e * (x i₀ ^ d' / aeval x s)) := by
    field_simp
  rw [this]
  exact mul_mem hf' hmem

theorem exists_pow_mul_mem_ampleRing (H : SubSystem S x Ω) (h b : Ω) (J : Chart x)
    (hb : b ∈ ampleRing H 1 h)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H 1 h I)
    {c : Ω} (hc : c ∈ chartRing S x J) : ∃ e : ℕ, b ^ e * c ∈ ampleRing H 1 h := by
  classical
  have hloc : ∀ I : Chart x, ∃ e : ℕ, b ^ e * c ∈ ampleChart H 1 h I := by
    intro I
    obtain ⟨e₀, he₀⟩ := hbJ I
    have hcU : c ∈ chartRing S x (chartUnion I J) := chartRing_mono Finset.subset_union_right hc
    obtain ⟨e₁, he₁⟩ := exists_pow_mul_mem_chartRing I J hcU
    refine ⟨e₀ * e₁, ?_⟩
    have hρσ : (xProd I ^ J.1.card / xProd J ^ I.1.card) *
        (xProd J ^ I.1.card / xProd I ^ J.1.card) = 1 := by
      have := xProd_ne_zero I
      have := xProd_ne_zero J
      field_simp
    have : b ^ (e₀ * e₁) * c = (b ^ e₀ * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ e₁ *
        ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e₁ * c) := by
      calc b ^ (e₀ * e₁) * c = (b ^ e₀) ^ e₁ * ((xProd I ^ J.1.card / xProd J ^ I.1.card) *
          (xProd J ^ I.1.card / xProd I ^ J.1.card)) ^ e₁ * c := by
            rw [hρσ, one_pow, mul_one, pow_mul]
        _ = _ := by ring
    rw [this]
    exact ampleChart_mul H h I (ampleChart_pow H h I he₀ e₁)
      (chartRing_subset_ampleChart H h I he₁)
  choose f hf using hloc
  refine ⟨∑ I, f I, Set.mem_iInter.mpr fun I => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (fun I _ => Nat.zero_le (f I)) (Finset.mem_univ I))
  have : b ^ (f I + k) * c = (b ^ f I * c) * b ^ k := by ring
  rw [hk, this]
  exact ampleChart_mul H h I (hf I) (ampleChart_pow H h I (Set.mem_iInter.mp hb I) k)

end GraphClosedAlt

end

end GroundTheory.Heights₂.Heights.Kleiman
