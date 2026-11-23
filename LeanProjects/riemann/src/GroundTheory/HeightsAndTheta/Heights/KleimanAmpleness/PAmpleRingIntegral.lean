import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AmpleRingIntegralSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

namespace AmpleRingIntegral

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem mem_valuationSubring {H : LineBundle S x} (D : AmpleData S x H) (j : Fin (D.r + 1))
    (hj : D.h j ≠ 0) (hne : (support x).Nonempty) (V : ValuationSubring Ω)
    (hV : (ampleBase (S := S) D.h j : Set Ω) ⊆ V) {f : Ω}
    (hf : f ∈ ampleRing H.toSubSystem D.m (D.h j)) : f ∈ V := by
  set v := V.valuation
  have hVle : ∀ {a : Ω}, a ∈ V → v a ≤ 1 := fun ha => (V.valuation_le_one_iff _).mpr ha
  obtain ⟨i, hi, hmax⟩ := (support x).exists_max_image (fun a => v (x a)) hne
  have hxi : x i ≠ 0 := (mem_support x).mp hi
  set I : Chart x := singleChart hxi

  let Vs : Subalgebra S Ω :=
    { V.toSubring with algebraMap_mem' := fun r => hV (Subalgebra.algebraMap_mem _ r) }
  have hA : ∀ a ∈ chartRing S x I, a ∈ V := by
    intro a ha
    have hB := mem_ampleBase_of_mem_chartRing hxi ha
    refine (Algebra.adjoin_le (S := Vs) ?_) hB
    rintro _ ⟨l, rfl⟩
    by_cases hl : x l = 0
    · simp only [hl, zero_div]; exact V.zero_mem
    · refine V.mem_of_valuation_le_one _ ?_
      have hvi : v (x i) ≠ 0 := (Valuation.ne_zero_iff _).mpr hxi
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hvi)]
      exact hmax l ((mem_support x).mpr hl)

  obtain ⟨Q', hQ'⟩ := H.invertible I
  have hPQ : H.toSubSystem.sub I ^ D.m * Q' ^ D.m = 1 := by
    rw [← mul_pow]; exact (congrArg (· ^ D.m) hQ').trans (one_pow _)
  have hgen : H.toSubSystem.sub I ^ D.m = Submodule.span (chartRing S x I) (Set.range D.h) := by
    rw [← SubSystem.pow_sub, D.generates I]

  have hunit : ∃ l, ∃ w ∈ Q' ^ D.m, 1 ≤ v (D.h l * w) := by
    by_contra hcon
    push Not at hcon
    have hone : (1 : Ω) ∈ H.toSubSystem.sub I ^ D.m * Q' ^ D.m :=
      hPQ ▸ Submodule.mem_one.mpr ⟨1, map_one _⟩
    rw [hgen] at hone
    have : v 1 < 1 := by
      refine Submodule.mul_induction_on hone (fun p hp w hw => ?_) (fun a b ha hb => v.map_add_lt ha hb)
      induction hp using Submodule.span_induction with
      | mem y hy => obtain ⟨l, rfl⟩ := hy; exact hcon l w hw
      | zero => simp
      | add a b _ _ ha hb => rw [add_mul]; exact v.map_add_lt ha hb
      | smul c a _ ha =>
        rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hVle (hA _ c.2))) ha
    simp at this
  obtain ⟨l, w, hw, hlw⟩ := hunit

  have hjw : 1 ≤ v (D.h j * w) := by
    have hlj : v (D.h l / D.h j) ≤ 1 := hVle (hV (Algebra.subset_adjoin ⟨l, rfl⟩))
    have : D.h l * w = D.h l / D.h j * (D.h j * w) := by field_simp
    rw [this, map_mul] at hlw
    exact hlw.trans (mul_le_of_le_one_left' hlj)

  obtain ⟨n, hn⟩ := Set.mem_iInter.mp hf I
  rw [SubSystem.pow_sub, pow_mul] at hn
  have hmem : f * D.h j ^ n * w ^ n ∈ (H.toSubSystem.sub I ^ D.m) ^ n * (Q' ^ D.m) ^ n :=
    Submodule.mul_mem_mul hn (Submodule.pow_mem_pow _ hw n)
  rw [← mul_pow, hPQ, one_pow] at hmem
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp hmem
  have hle : v (f * D.h j ^ n * w ^ n) ≤ 1 := hVle (hy ▸ hA _ y.2)
  rw [mul_assoc, ← mul_pow, map_mul, map_pow] at hle
  exact V.mem_of_valuation_le_one _
    ((le_mul_of_one_le_right' (one_le_pow_of_one_le' hjw n)).trans hle)

end AmpleRingIntegral

theorem AmpleRingIntegral.proof : AmpleRingIntegral.Statement := by
  intro S _ N Ω _ _ x H D j hj f hf
  set B := ampleBase (S := S) D.h j
  rcases (support x).eq_empty_or_nonempty with hne | hne
  ·
    have hI : IsEmpty (Chart x) := ⟨fun I => by
      obtain ⟨i, hi⟩ := I.2.1
      have := I.2.2 hi; rw [hne] at this; exact absurd this (Finset.notMem_empty i)⟩
    obtain ⟨t, ht⟩ := D.finite j hj
    have htop : Submodule.span B (t : Set Ω) = ⊤ :=
      eq_top_iff.mpr fun z _ => ht (by simp [ampleRing])
    refine IsIntegral.of_mem_of_fg (⊤ : Subalgebra B Ω) ?_ f trivial
    rw [Algebra.top_toSubmodule, ← htop]
    exact ⟨t, rfl⟩
  · have key : f ∈ ⨅ V : {V : ValuationSubring Ω // (B : Set Ω) ⊆ V.toSubring}, V.1.toSubring :=
      Subring.mem_iInf.mpr fun V => AmpleRingIntegral.mem_valuationSubring D j hj hne V.1 V.2 hf
    rw [iInf_valuationSubring_superset] at key
    have hcl : Subring.closure (B : Set Ω) = B.toSubring := Subring.closure_eq B.toSubring
    rw [hcl] at key
    exact key

end GroundTheory.Heights₂.Heights.Kleiman
