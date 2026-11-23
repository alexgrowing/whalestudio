import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem sum_char_dot_eq_zero {B : Type} [CommRing B] [Fintype B] (χ : AddChar B ℂ)
    (hχ : χ.IsPrimitive) {m : ℕ} (t : Fin m → B) (ht : t ≠ 0) :
    ∑ s : Fin m → B, χ (∑ a, s a * t a) = 0 := by
  let f : (Fin m → B) →+ B :=
    { toFun := fun s => ∑ a, s a * t a
      map_zero' := by simp
      map_add' := fun s s' => by simp [add_mul, Finset.sum_add_distrib] }
  have h : χ.compAddMonoidHom f ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := Function.ne_iff.1 ht
    refine hχ ha ?_
    ext r
    have h1 := DFunLike.congr_fun h0 (Pi.single a r)
    simpa [f, Pi.single_apply, mul_comm] using h1
  exact AddChar.sum_eq_zero_iff_ne_zero.2 h

theorem exists_dot_eq_of_indep {B : Type} [CommRing B] [Fintype B] (χ : AddChar B ℂ)
    (hχ : χ.IsPrimitive) {k n : ℕ} (x : Fin k → Fin n → B)
    (hx : ∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) (u : Fin k → B) :
    ∃ z : Fin n → B, ∀ a, ∑ i, x a i * z i = u a := by
  by_contra hne
  push_neg at hne
  have h1 : ∑ z : Fin n → B, ∑ s : Fin k → B, χ (∑ a, s a * (∑ i, x a i * z i - u a)) = 0 := by
    refine Finset.sum_eq_zero fun z _ => ?_
    refine sum_char_dot_eq_zero χ hχ (fun a => ∑ i, x a i * z i - u a) ?_
    obtain ⟨a, ha⟩ := hne z
    intro h0
    exact ha (sub_eq_zero.1 (congrFun h0 a))
  rw [Finset.sum_comm, Finset.sum_eq_single (0 : Fin k → B)] at h1
  · simp at h1
  · intro s _ hs
    have h2 : ∀ z : Fin n → B, χ (∑ a, s a * (∑ i, x a i * z i - u a)) =
        χ (∑ i, z i * (∑ a, s a • x a) i) * χ (-∑ a, s a * u a) := by
      intro z
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, sub_eq_add_neg, mul_add, Finset.sum_add_distrib, mul_neg,
        Finset.sum_neg_distrib]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    simp only [h2]
    rw [← Finset.sum_mul, sum_char_dot_eq_zero χ hχ _ (fun h => hs (hx s h)), zero_mul]
  · simp

theorem prim_of_indep_of_isPrimitive : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B),
    (∀ u, c (c u) = u) → ∀ (χ : AddChar B ℂ), χ.IsPrimitive →
    ∀ (k n : ℕ) (x : Fin k → Fin n → B),
      (∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) → Prim c x := by
  intro B _ _ c hc χ hχ k n x hx
  choose z hz using fun b : Fin k => exists_dot_eq_of_indep χ hχ x hx (Pi.single b 1)
  refine ⟨fun b i => c (z b i), fun a b => ?_⟩
  simp only [ip, hc]
  rw [hz, Pi.single_apply]

end GlobalTheory.GramCount
