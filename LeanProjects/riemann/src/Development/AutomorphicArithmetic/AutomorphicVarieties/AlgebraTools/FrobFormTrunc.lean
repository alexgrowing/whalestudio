import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.frob_form_trunc :
    ∀ {k : Type} [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) k] (m : ℕ), ∃ lam : (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ (m + 1)}) →+ ZMod l, (∀ f, lam (Ideal.Quotient.mk _ f) = Algebra.trace (ZMod l) k (PowerSeries.coeff m f)) ∧ (∀ x, (∀ y, lam (x * y) = 0) → x = 0) ∧ Finite (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ (m + 1)}) := by
  intro k _ _ l _ _ m
  classical
  let I : Ideal (PowerSeries k) := Ideal.span {(PowerSeries.X : PowerSeries k) ^ (m + 1)}
  have hmem : ∀ f : PowerSeries k, f ∈ I ↔ ∀ j, j < m + 1 → PowerSeries.coeff j f = 0 := by
    intro f
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  have hW : ∀ f g : PowerSeries k, Ideal.Quotient.mk I f = Ideal.Quotient.mk I g →
      ∀ j, j < m + 1 → PowerSeries.coeff j f = PowerSeries.coeff j g := by
    intro f g h j hj
    rw [Ideal.Quotient.eq, hmem] at h
    have := h j hj
    rw [map_sub, sub_eq_zero] at this
    exact this
  let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  have hs : ∀ x, Ideal.Quotient.mk I (s x) = x := Function.surjInv_eq _
  let L : (PowerSeries k ⧸ I) → ZMod l := fun x => Algebra.trace (ZMod l) k (PowerSeries.coeff m (s x))
  have hL : ∀ f, L (Ideal.Quotient.mk I f) = Algebra.trace (ZMod l) k (PowerSeries.coeff m f) := by
    intro f
    simp only [L]
    rw [hW _ _ (hs _) m (Nat.lt_succ_self m)]
  let lam : (PowerSeries k ⧸ I) →+ ZMod l :=
    { toFun := L
      map_zero' := by
        have := hL 0
        rw [map_zero, map_zero, map_zero] at this
        exact this
      map_add' := by
        intro x y
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [← map_add, hL, hL, hL, map_add, map_add] }
  refine ⟨lam, hL, ?_, ?_⟩
  · intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    by_contra hne
    have hnot : f ∉ I := fun h => hne (Ideal.Quotient.eq_zero_iff_mem.2 h)
    rw [hmem] at hnot
    push_neg at hnot
    obtain ⟨j, hj, hfj⟩ := hnot
    have hnd := (traceForm_nondegenerate (ZMod l) k).1 (PowerSeries.coeff j f)
    have hex : ∃ b : k, Algebra.trace (ZMod l) k (PowerSeries.coeff j f * b) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hfj (hnd fun b => by rw [Algebra.traceForm_apply]; exact hc b)
    obtain ⟨b, hb⟩ := hex
    apply hb
    have := hx (Ideal.Quotient.mk I (PowerSeries.C b * PowerSeries.X ^ (m - j)))
    rw [← map_mul] at this
    change L _ = 0 at this
    rw [hL] at this
    have hjm : j ≤ m := Nat.lt_succ_iff.mp hj
    have hc : PowerSeries.coeff m (f * (PowerSeries.C b * PowerSeries.X ^ (m - j))) =
        PowerSeries.coeff j f * b := by
      rw [show f * (PowerSeries.C b * PowerSeries.X ^ (m - j)) =
          PowerSeries.C b * (PowerSeries.X ^ (m - j) * f) by ring]
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (Nat.sub_le m j),
        Nat.sub_sub_self hjm, mul_comm]
    rw [hc] at this
    exact this
  · let e : (PowerSeries k ⧸ I) → (Fin (m + 1) → k) := fun x j => PowerSeries.coeff j (s x)
    apply Finite.of_injective e
    intro x y hxy
    rw [← hs x, ← hs y, Ideal.Quotient.eq, hmem]
    intro j hj
    have := congrFun hxy ⟨j, hj⟩
    rw [map_sub, sub_eq_zero]
    exact this
