import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjEmbeddingRt

noncomputable section

namespace GlobalTheory.HostModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem coe_rt_sq (H : Host E) : (H.rt : E) ^ 2 = -(H.d : E) := by
  have h := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  simpa using h

theorem conj_embedding_rt (H : Host E) (τ : E →+* ℂ) :
    starRingEnd ℂ (τ (H.rt : E)) = -τ (H.rt : E) :=
  _root_.UpperTheory.Reformulated.B.Gc4.conj_embedding_rt H τ

@[simp] theorem bar_rt (H : Host E) : H.bar H.rt = -H.rt := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply RingOfIntegers.ext
  apply τ.injective
  have h := IsCMField.complexEmbedding_complexConj E τ (H.rt : E)
  rw [H.bar_eq, h, conj_embedding_rt]
  simp

@[simp] theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

@[simp] theorem cmHost_bar_halfIntegerGenerator (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  have h := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, bar_rt, map_one, map_ofNat] at h
  apply mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 E) ≠ 0)
  rw [h, mul_sub, H.two_weight_eq_one_add_root]; ring

theorem rt_eq (H : Host E) : H.rt = 2 * H.w0 - 1 := by
  rw [H.two_weight_eq_one_add_root]; ring

theorem rt_mem_adjoin (H : Host E) : H.rt ∈ Algebra.adjoin ℤ {H.w0} := by
  rw [rt_eq]
  exact sub_mem (mul_mem (ofNat_mem _ 2) (Algebra.self_mem_adjoin_singleton ℤ _)) (one_mem _)

theorem rt_ne_zero (H : Host E) : H.rt ≠ 0 := by
  intro h
  have h2 := H.rt_sq
  rw [h] at h2
  have : (H.d : 𝓞 E) = 0 := by simpa using h2.symm
  exact H.d_prime.ne_zero (by exact_mod_cast this)

theorem two_sub_rt_mul_two_add_rt (H : Host E) : (2 - H.rt) * (2 + H.rt) = ((H.d + 4 : ℕ) : 𝓞 E) := by
  have h := H.rt_sq
  push_cast
  linear_combination -h

theorem map_bar_span_two_sub_rt (H : Host E) :
    (Ideal.span {2 - H.rt}).map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {2 + H.rt} := by
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  change H.bar (2 - H.rt) = _
  rw [map_sub, bar_rt, map_ofNat, sub_neg_eq_add]

theorem isCoprime_two_sub_rt_two_add_rt (H : Host E) : IsCoprime (2 - H.rt) (2 + H.rt) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d = 4 * k + 3 := ⟨H.d / 4, by have := H.d_mod; omega⟩
  have h := H.rt_sq
  rw [hk] at h
  push_cast at h
  refine ⟨(k : 𝓞 E) + 2 - (2 + H.rt), (k : 𝓞 E) + 2, ?_⟩
  linear_combination h

def level (H : Host E) (A : ℕ) (hA : 0 < A) : Level H where
  M := H.d + 4
  three_le := by omega
  odd := by
    have := H.d_mod
    exact Nat.odd_iff.mpr (by omega)
  Mb := Ideal.span {2 - H.rt}
  fromK := by
    apply le_antisymm
    · apply Ideal.span_mono
      rintro a rfl
      exact ⟨Ideal.mem_span_singleton_self _, sub_mem (ofNat_mem _ 2) (rt_mem_adjoin H)⟩
    · exact Ideal.span_le.mpr fun a ha => ha.1
  prod := by
    rw [map_bar_span_two_sub_rt, Ideal.span_singleton_mul_span_singleton, two_sub_rt_mul_two_add_rt]
  coprime := by
    rw [map_bar_span_two_sub_rt, ← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact isCoprime_two_sub_rt_two_add_rt H
  A := A
  A_pos := hA

@[simp] theorem level_M (H : Host E) (A : ℕ) (hA : 0 < A) : (level H A hA).M = H.d + 4 := rfl

@[simp] theorem level_Mb (H : Host E) (A : ℕ) (hA : 0 < A) :
    (level H A hA).Mb = Ideal.span {2 - H.rt} := rfl

@[simp] theorem level_A (H : Host E) (A : ℕ) (hA : 0 < A) : (level H A hA).A = A := rfl

theorem Mb_ne_top {H : Host E} (l : Level H) : l.Mb ≠ ⊤ := by
  intro h
  have hp := l.prod
  rw [h, Ideal.map_top, Ideal.top_mul, eq_comm, Ideal.span_singleton_eq_top] at hp
  have h1 : IsUnit ((l.M : ℤ)) := by
    have hint : Algebra.IsIntegral ℤ (𝓞 E) := inferInstance
    have := (isUnit_map_iff (algebraMap ℤ (𝓞 E)) (l.M : ℤ)).mp (by simpa using hp)
    exact this
  have h3 := l.three_le
  rcases Int.isUnit_iff.mp h1 with h2 | h2 <;> omega

theorem level_goodAt (H : Host E) (A : ℕ) (hA : 0 < A) {p : ℕ} (hp : ¬ p ∣ H.d + 4) :
    (level H A hA).GoodAt p := by
  unfold Level.GoodAt
  rw [level_M, Nat.factorization_eq_zero_of_not_dvd hp]
  simp

instance instNonemptyLevel (H : Host E) : Nonempty (Level H) := ⟨level H 1 one_pos⟩

example (H : Host E) (h : H.d = 7) : (level H 5 (by norm_num)).M' = 55 := by
  simp only [Level.M', level_M, level_A, h]
  decide

example (H : Host E) : H.bar H.rt ≠ H.rt := by
  rw [bar_rt]
  intro h
  apply rt_ne_zero H
  have : (2 : 𝓞 E) * H.rt = 0 := by linear_combination -h
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

example (H : Host E) (A : ℕ) (hA : 0 < A) :
    (level H A hA).Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ (level H A hA).Mb := by
  intro h
  have := (level H A hA).coprime
  rw [h, sup_idem] at this
  exact Mb_ne_top _ this

example (H : Host E) : (level H 1 one_pos).GoodAt 2 :=
  level_goodAt H 1 one_pos (by have := H.d_mod; omega)

end GlobalTheory.HostModel
