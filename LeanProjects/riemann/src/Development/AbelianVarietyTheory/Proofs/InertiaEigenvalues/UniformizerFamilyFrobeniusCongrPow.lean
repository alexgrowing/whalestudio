import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section
variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

theorem zero_mem_QSet_goodU : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW]
  simp

theorem uPow_mem_QSet_goodU [CharZero K] (m : ℕ) :
    (fun _ => C (X ^ m) : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨fun p => if p = (0, m) then ((dpDen e 0 m : ℕ) : Wq l a) else 0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW, coeff_C]
  by_cases h : (i, n) = (0, m)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have : (dpDen e 0 n : K) ≠ 0 := Nat.cast_ne_zero.mpr (dpDen_pos e 0 n).ne'
    simp only [if_true, map_natCast, coeff_X_pow_self]
    exact div_self this
  · rw [if_neg h]
    simp only [map_zero, zero_div]
    by_cases hi : i = 0
    · subst hi
      have hn : n ≠ m := fun hn => h (by rw [hn])
      rw [if_pos rfl, coeff_X_pow, if_neg hn]
    · rw [if_neg hi, map_zero]

end

theorem uFam_mem_GoodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → uFam a K ∈ GoodSet t e φ₂ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hf : frob2 φ₂ (uFam a K) = (fun _ => C (X ^ l) : ZMod a → K⟦X⟧⟦X⟧) := by
    funext τ
    show φ₂ (C X) = _
    rw [hC, frob_X]
  refine ⟨?_, ?_, 0, zero_mem_QSet_goodU t K e, ?_⟩
  · have := uPow_mem_QSet_goodU t K e 1
    rw [pow_one] at this
    exact this
  · rw [hf]; exact uPow_mem_QSet_goodU t K e l
  · rw [hf, mul_zero, add_zero]
    funext τ
    simp [uFam]

end GlobalTheory.CrysPrism
