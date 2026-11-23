import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKReal

theorem constantCoeff_frobS_apply (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (p : (Wq l a)⟦X⟧) :
    constantCoeff (frobS l a p) = sigma l a (constantCoeff p) := by
  simp only [frobS]
  simp only [RingHom.coe_comp, Function.comp_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
  simp

theorem eisPoly_distinguished_complete : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → IsUnit ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) ∧ IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)}) (Wq l a)⟦X⟧ := by
  intro l _ a _ Ep ⟨hmon, hdeg, hdvd, w, hw⟩
  constructor
  · have hφ := (deltaS l a).φ_eq (Ep : (Wq l a)⟦X⟧)
    have h1 := congrArg constantCoeff hφ
    rw [show (deltaS l a).φ (Ep : (Wq l a)⟦X⟧) = frobS l a Ep from rfl, constantCoeff_frobS_apply] at h1
    simp only [Polynomial.constantCoeff_coe, map_add, map_pow, map_mul, map_natCast, hw] at h1
    set c := constantCoeff ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) with hc
    obtain ⟨k, hk⟩ : ∃ k, l = k + 2 := ⟨l - 2, by have := (Fact.out : l.Prime).two_le; omega⟩
    have h2 : c = sigma l a (w : Wq l a) - (l : Wq l a) ^ (k + 1) * (w : Wq l a) ^ l := by
      have hl0 : (l : Wq l a) ≠ 0 := WittVector.p_nonzero l (Fq l a)
      apply mul_left_cancel₀ hl0
      have : ((l : Wq l a) * w) ^ l = (l : Wq l a) * ((l : Wq l a) ^ (k + 1) * (w : Wq l a) ^ l) := by
        have e : (l : Wq l a) ^ l = (l : Wq l a) ^ (k + 2) := by rw [← hk]
        rw [mul_pow, e]; ring
      rw [this] at h1
      linear_combination -h1
    rw [isUnit_iff_constantCoeff, ← hc, h2]
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [← WittVector.constantCoeff_apply]
    simp only [map_sub, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow k.succ_ne_zero, zero_mul, sub_zero]
    rw [WittVector.constantCoeff_apply, coeff_sigma, ← WittVector.constantCoeff_apply]
    exact pow_ne_zero _ ((w.isUnit.map (WittVector.constantCoeff (p := l) (R := Fq l a))).ne_zero)
  · set e := Ep.natDegree with he
    haveI : NeZero e := ⟨hdeg.ne'⟩
    have hP : Polynomial.C (l : Wq l a) ∣ Ep - Polynomial.X ^ e := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases lt_trichotomy i e with h | rfl | h
      · rw [if_neg h.ne, sub_zero]; exact hdvd i h
      · have h1 : Ep.coeff e = 1 := hmon.coeff_natDegree
        rw [if_pos rfl, h1, sub_self]; exact dvd_zero _
      · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_zero]; exact dvd_zero _
    obtain ⟨q, hq⟩ := hP
    have hS : (Ep : (Wq l a)⟦X⟧) = X ^ e + (l : (Wq l a)⟦X⟧) * (q : (Wq l a)⟦X⟧) := by
      have := congrArg (fun p : Polynomial (Wq l a) => (p : (Wq l a)⟦X⟧)) hq
      simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul,
        map_natCast] at this
      have hc : ((l : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) = l := map_natCast (Polynomial.coeToPowerSeries.ringHom (R := Wq l a)) l
      rw [hc] at this
      linear_combination this
    have hJ : Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)} =
        Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {eis l a e} := by
      apply le_antisymm
      · refine sup_le le_sup_left ?_
        rw [Ideal.span_singleton_le_iff_mem, hS,
          show (X : (Wq l a)⟦X⟧) ^ e + (l : (Wq l a)⟦X⟧) * q = eis l a e + (l : (Wq l a)⟦X⟧) * (q - 1) by
            rw [eis]; ring]
        exact add_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      · refine sup_le le_sup_left ?_
        rw [Ideal.span_singleton_le_iff_mem,
          show eis l a e = (Ep : (Wq l a)⟦X⟧) + (l : (Wq l a)⟦X⟧) * (1 - q) by rw [eis, hS]; ring]
        exact add_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    rw [hJ]
    exact complete_eis l a e

end GlobalTheory.BKReal
