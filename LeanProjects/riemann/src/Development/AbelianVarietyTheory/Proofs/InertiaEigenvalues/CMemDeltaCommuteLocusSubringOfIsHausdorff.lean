import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaAddSubMemPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.WDelta

variable {l : ℕ} {A : Type} [CommRing A]

theorem δ_pow_succ (D : Delta l A) (z : A) (m : ℕ) :
    ∃ c, D.δ (z ^ (m + 1)) = ((m + 1 : ℕ) : A) * z ^ (l * m) * D.δ z + (l : A) * D.δ z ^ 2 * c := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨z ^ l * c + ((m + 1 : ℕ) : A) * z ^ (l * m) + (l : A) * D.δ z * c, ?_⟩
    have e1 : (z ^ (m + 1)) ^ l = z ^ (l * m) * z ^ l := by rw [← pow_mul, ← pow_add]; ring_nf
    have e2 : z ^ (l * (m + 1)) = z ^ (l * m) * z ^ l := by rw [← pow_add]; ring_nf
    rw [pow_succ z (m + 1), D.δ_mul, hc, e1, e2]
    push_cast
    ring

theorem δ_pow_pow [hl : Fact l.Prime] (D : Delta l A) (y : A) (n : ℕ) :
    D.δ (y ^ (l ^ n)) ∈ Ideal.span {(l : A)} ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := δ_pow_succ D (y ^ (l ^ n)) (l - 1)
    rw [Nat.sub_add_cancel hl.out.one_le] at hc
    rw [pow_succ l n, pow_mul, hc, pow_succ]
    have : ((l : ℕ) : A) * (y ^ l ^ n) ^ (l * (l - 1)) * D.δ (y ^ l ^ n) + (l : A) * D.δ (y ^ l ^ n) ^ 2 * c =
        D.δ (y ^ l ^ n) * ((l : A) * ((y ^ l ^ n) ^ (l * (l - 1)) + D.δ (y ^ l ^ n) * c)) := by ring
    rw [this]
    exact Ideal.mul_mem_mul ih (Ideal.mem_span_singleton.2 (dvd_mul_right _ _))

theorem eq_zero_of_mem_pow {C : Type} [CommRing C] {J : Ideal C} (h : IsHausdorff J C) {x : C}
    (hx : ∀ n, x ∈ J ^ n) : x = 0 :=
  h.haus x fun n => by rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]; exact hx n

variable (l) (a : ℕ) [hl : Fact l.Prime] [NeZero a]

theorem teich_eq_pow (n : ℕ) (x : Fq l a) :
    ∃ y : Fq l a, WittVector.teichmuller l x = WittVector.teichmuller l y ^ (l ^ n) := by
  induction n with
  | zero => exact ⟨x, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨y ^ (l ^ (a - 1)), ?_⟩
    have h1 : (y ^ (l ^ (a - 1))) ^ l = y := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (NeZero.pos a)]; exact Fq.pow_card y
    rw [hy, pow_succ' l n, pow_mul, ← map_pow (WittVector.teichmuller l) (y ^ l ^ (a - 1)) l, h1]

theorem deltaS_C_teich (x : Fq l a) :
    (deltaS l a).δ (PowerSeries.C (WittVector.teichmuller l x)) = 0 := by
  have h := (deltaS l a).φ_eq (PowerSeries.C (WittVector.teichmuller l x))
  have h2 : (deltaS l a).φ (PowerSeries.C (WittVector.teichmuller l x)) =
      PowerSeries.C (WittVector.teichmuller l x) ^ l := by
    change frobS l a _ = _
    have := sigma_pow_teich l a 1 x
    rw [pow_one, pow_one] at this
    rw [frobS_C, this, map_pow]
  rw [h2, left_eq_add] at h
  exact (mul_eq_zero.1 h).resolve_left (l_ne_zero l a)

variable {l a}

theorem C_teich_mem {C : Type} [CommRing C] (DC : Delta l C) {J : Ideal C} (hl : (l : C) ∈ J)
    (hJ : IsHausdorff J C) (σ : (Wq l a)⟦X⟧ →+* C) (x : Fq l a) :
    PowerSeries.C (WittVector.teichmuller l x) ∈ δLocus (deltaS l a) DC σ := by
  rw [mem_δLocus, deltaS_C_teich, map_zero]
  refine (eq_zero_of_mem_pow hJ fun n => ?_).symm
  obtain ⟨y, hy⟩ := teich_eq_pow l a n x
  rw [hy, map_pow, map_pow]
  exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem J).2 hl) n (δ_pow_pow DC _ n)

theorem approx (S : Subring (Wq l a)) (hS : ∀ x, WittVector.teichmuller l x ∈ S) (n : ℕ) (w : Wq l a) :
    ∃ s ∈ S, ∃ v, w - s = (l : Wq l a) ^ n * v := by
  induction n with
  | zero => exact ⟨0, S.zero_mem, w, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs, v, hv⟩ := ih
    have h : v - WittVector.teichmuller l (v.coeff 0) ∈ Ideal.span {(l : Wq l a)} := by
      rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self]
    obtain ⟨v', hv'⟩ := Ideal.mem_span_singleton.1 h
    refine ⟨s + (l : Wq l a) ^ n * WittVector.teichmuller l (v.coeff 0),
      S.add_mem hs (S.mul_mem (S.pow_mem (natCast_mem S l) n) (hS _)), v', ?_⟩
    rw [pow_succ, mul_assoc, ← hv']
    linear_combination hv

end GlobalTheory.BSP.WDelta

namespace GlobalTheory.BSP

open GlobalTheory.BSP.WDelta in

theorem C_mem_δLocus_of_hausdorff : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C]
    (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ σ : (Wq l a)⟦X⟧ →+* C,
    ∀ w : Wq l a, PowerSeries.C w ∈ δLocus (deltaS l a) DC σ := by
  intro l _ a _ C _ DC J hl hJ σ w
  let S : Subring (Wq l a) := (δLocus (deltaS l a) DC σ).comap PowerSeries.C
  rw [mem_δLocus, ← sub_eq_zero]
  refine eq_zero_of_mem_pow hJ fun n => ?_
  obtain ⟨s, hs, v, hv⟩ := approx S (fun x => C_teich_mem DC hl hJ σ x) (n + 1) w
  have hs' := mem_δLocus.1 (Subring.mem_comap.1 hs)
  have hy : PowerSeries.C w - PowerSeries.C s = (l : (Wq l a)⟦X⟧) ^ (n + 1) * PowerSeries.C v := by
    rw [← map_sub, hv, map_mul, map_pow, map_natCast]
  have h1 := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l (Wq l a)⟦X⟧ (deltaS l a) (Ideal.span {(l : (Wq l a)⟦X⟧)})
    (Ideal.mem_span_singleton_self _) n (PowerSeries.C s) (PowerSeries.C w - PowerSeries.C s)
    (by rw [hy, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _))
  rw [add_sub_cancel, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨r, hr⟩ := h1
  have h2 := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l C DC J hl n (σ (PowerSeries.C s)) (σ (PowerSeries.C w - PowerSeries.C s))
    (by rw [hy, map_mul, map_pow, map_natCast]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl _))
  rw [← map_add, add_sub_cancel] at h2
  have h3 : σ ((deltaS l a).δ (PowerSeries.C w)) - σ ((deltaS l a).δ (PowerSeries.C s)) ∈ J ^ n := by
    rw [← map_sub, hr, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl _)
  have := (J ^ n).sub_mem h3 h2
  rw [hs'] at this
  convert this using 1
  ring

end GlobalTheory.BSP
