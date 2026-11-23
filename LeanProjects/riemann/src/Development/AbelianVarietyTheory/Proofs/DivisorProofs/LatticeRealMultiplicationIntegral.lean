import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
open NumberField GlobalTheory.RealMult

namespace GlobalTheory.RealMult

theorem exists_trace_pairing_of_integral : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (Λ : Submodule ℤ (Fin (Module.finrank ℚ F) → ℂ)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (h : Fin (Module.finrank ℚ F) → ℝ),
    (∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ Λ → (fun j ↦ (e j (a : F) : ℂ) * l j) ∈ Λ) →
    (∀ (c' : 𝔠.elt) (l l' : Λ), ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (((e j ((c' : F) / (2 * (c : F))) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im = n) →
    ∃ P : Λ → Λ → F, (∀ l l' : Λ, P l l' = -P l' l) ∧ (∀ l₁ l₂ l' : Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') ∧
      (∀ (a : 𝓞 F) (l l' al : Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') ∧
      (∀ l l' : Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) ∧
      (∀ l l' : Λ, P l l' ∈ dualLat 𝔠) := by
  intro F _ _ _ 𝔠 c hc Λ e h hΛ hint
  have hc0 : (c : F) ≠ 0 := by
    intro h0
    have := hc (e ⟨0, Module.finrank_pos⟩)
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  let G : Λ → Λ → Fin (Module.finrank ℚ F) → ℝ := fun l l' j =>
    h j * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j)).im
  have conv : ∀ (t : F) (l l' : Λ), (∑ j, (h j : ℂ) * (((e j t : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im = ∑ j, e j t * G l l' j := by
    intro t l l'
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [G]
    rw [Complex.im_ofReal_mul, mul_assoc, Complex.im_ofReal_mul]; ring
  have rat : ∀ (l l' : Λ) (t : F), ∃ q : ℚ, (q : ℝ) = ∑ j, e j t * G l l' j := by
    intro l l' t
    obtain ⟨y, hy0, hyi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic t)).exists_integral_multiple
    let x : 𝓞 F := ⟨y • t, hyi⟩
    have hx : ((x : 𝓞 F) : F) = (y : F) * t := by
      show y • t = _
      rw [zsmul_eq_mul]
    let c' : 𝔠.elt := ⟨((2 : 𝓞 F) * x) • (c : F), Submodule.smul_mem _ _ c.2⟩
    obtain ⟨k, hk⟩ := hint c' l l'
    have hq : (c' : F) / (2 * c) = (y : F) * t := by
      show (((2 : 𝓞 F) * x) • (c : F)) / (2 * c) = _
      rw [Algebra.smul_def, map_mul, map_ofNat]
      change 2 * ((x : 𝓞 F) : F) * (c : F) / (2 * c) = _
      rw [hx]
      field_simp
    rw [conv, hq] at hk
    refine ⟨(k : ℚ) / y, ?_⟩
    have hsum : ∑ j, e j ((y : F) * t) * G l l' j = (y : ℝ) * ∑ j, e j t * G l l' j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_intCast]; ring
    rw [hsum] at hk
    have hy : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
    push_cast
    rw [← hk]
    field_simp
  have hnd := traceForm_nondegenerate ℚ F
  have exQ : ∀ l l' : Λ, ∃ Q : F, ∀ t : F,
      ((Algebra.trace ℚ F (t * Q) : ℚ) : ℝ) = ∑ j, e j t * G l l' j := by
    intro l l'
    choose q hq using rat l l'
    let φ : Module.Dual ℚ F :=
      { toFun := q
        map_add' := fun x y => by
          apply Rat.cast_injective (α := ℝ)
          push_cast
          rw [hq, hq, hq, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_add]; ring
        map_smul' := fun r x => by
          apply Rat.cast_injective (α := ℝ)
          simp only [RingHom.id_apply, smul_eq_mul]
          push_cast
          rw [hq, hq, Rat.smul_def, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, map_ratCast]; ring }
    refine ⟨((Algebra.traceForm ℚ F).toDual hnd).symm φ, fun t => ?_⟩
    rw [mul_comm, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
    exact hq t
  choose Q hQ using exQ
  have uniq : ∀ x y : F, (∀ t : F, ((Algebra.trace ℚ F (t * x) : ℚ) : ℝ) =
      ((Algebra.trace ℚ F (t * y) : ℚ) : ℝ)) → x = y := by
    intro x y hxy
    apply ((Algebra.traceForm ℚ F).toDual hnd).injective
    refine LinearMap.ext fun t => ?_
    rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply,
      Algebra.traceForm_apply, mul_comm x, mul_comm y]
    exact_mod_cast hxy t
  refine ⟨fun l l' => Q l l' / (2 * c), ?_, ?_, ?_, ?_, ?_⟩
  · intro l l'
    simp only
    rw [← neg_div]; congr 1
    apply uniq; intro t
    rw [mul_neg, map_neg, Rat.cast_neg, hQ, hQ, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [G, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  · intro l₁ l₂ l'
    simp only
    rw [← add_div]; congr 1
    apply uniq; intro t
    rw [mul_add, map_add, Rat.cast_add, hQ, hQ, hQ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [G, Submodule.coe_add, Pi.add_apply, add_mul, Complex.add_im]
    ring
  · intro a l l' al hal
    simp only
    rw [← mul_div_assoc]; congr 1
    apply uniq; intro t
    rw [← mul_assoc, hQ, hQ]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [G, hal, map_mul]
    rw [mul_assoc ((e j (a : F) : ℂ)), Complex.im_ofReal_mul]
    ring
  · intro l l'
    have h1 := hQ l l' 1
    simp only [one_mul, map_one] at h1
    have htr : Algebra.trace ℚ F ((c : F) * (Q l l' / (2 * c))) = Algebra.trace ℚ F (Q l l') / 2 := by
      rw [show (c : F) * (Q l l' / (2 * c)) = (1 / 2 : ℚ) • Q l l' by
        rw [Rat.smul_def]; push_cast; field_simp]
      rw [map_smul, smul_eq_mul]; ring
    rw [htr, Complex.im_sum]
    simp_rw [Complex.im_ofReal_mul]
    push_cast
    rw [h1]
    ring
  · intro l l'
    have hI : ((𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) ≠ 0 := 𝔠.ne_zero
    unfold dualLat
    rw [FractionalIdeal.mem_dual hI]
    intro a ha
    obtain ⟨k, hk⟩ := hint ⟨a, ha⟩ l l'
    rw [conv] at hk
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply]
    apply Rat.cast_injective (α := ℝ)
    rw [show Q l l' / (2 * c) * a = (a / (2 * c)) * Q l l' by ring, hQ]
    simp only [eq_intCast, Rat.cast_intCast]
    exact hk.symm

end GlobalTheory.RealMult
