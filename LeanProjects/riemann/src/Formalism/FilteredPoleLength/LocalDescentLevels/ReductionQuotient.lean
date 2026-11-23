import Formalism.FilteredPoleLength.ReducedBasisBounds.ReductionQuotient
import Formalism.LogFactorialIndices.LogProductFormula

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

namespace BasisReduction

open Formalism.LatticeIndexTer.subgroupData

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

abbrev q (A B : Submodule O X) : ℕ∞ := Module.length O (↥A ⧸ B.comap A.subtype)

theorem q_congr (A : Submodule O X) {B B' : Submodule O X} (h : A ⊓ B = A ⊓ B') :
    q A B = q A B' := by
  have e : B.comap A.subtype = B'.comap A.subtype := by
    ext x
    simp only [Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · intro hx
      have : (x : X) ∈ A ⊓ B' := h ▸ Submodule.mem_inf.mpr ⟨x.2, hx⟩
      exact this.2
    · intro hx
      have : (x : X) ∈ A ⊓ B := h.symm ▸ Submodule.mem_inf.mpr ⟨x.2, hx⟩
      exact this.2
  unfold q
  rw [e]

theorem q_chain {A B C : Submodule O X} (hAB : A ≤ B) (hBC : B ≤ C) :
    q C A = q C B + q B A := by
  rw [add_comm]
  exact length_chain' hAB hBC

theorem q_sup (A B : Submodule O X) : q (A ⊔ B) B = q A B := by
  have h := (LinearMap.quotientInfEquivSupQuotient A B).length_eq
  have h2 : q A (A ⊓ B) = q A B := q_congr A (by simp)
  exact h.symm.trans h2

theorem q_zero {A B : Submodule O X} (h : A ≤ B) : q A B = 0 := qlen_eq_zero h

theorem len_comap_le {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (p : Submodule O M') :
    Module.length O (M ⧸ p.comap f) ≤ Module.length O (M' ⧸ p) := by
  apply Module.length_le_of_injective (Submodule.mapQ (p.comap f) p f le_rfl)
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [Submodule.mapQ_apply] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  simpa using hxy

theorem q_top (N : Submodule O X) : q ⊤ N = Module.length O (X ⧸ N) := by
  apply le_antisymm
  · exact len_comap_le _ _
  · have h := len_comap_le (Submodule.topEquiv (R := O) (M := X)).symm.toLinearMap
      (N.comap (⊤ : Submodule O X).subtype)
    refine le_trans (le_of_eq ?_) h
    congr 2

end BasisReduction

open BasisReduction

theorem filteredLength : FilteredLength := by
  intro O A _ _ _ n F h0 hn hF N
  have key : ∀ k, Module.length O (A ⧸ N) =
      ∑ j ∈ Finset.range k, q (F j) (F (j + 1) ⊔ (N ⊓ F j)) + q (F k) N := by
    intro k
    induction k with
    | zero => simp [h0, q_top]
    | succ k ih =>
      rw [ih, Finset.sum_range_succ, add_assoc]
      congr 1
      have hB : F (k + 1) ⊔ (N ⊓ F k) ≤ F k := sup_le (hF k) inf_le_right
      calc q (F k) N = q (F k) (N ⊓ F k) := q_congr _ (by rw [inf_comm N, ← inf_assoc, inf_idem])
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1) ⊔ (N ⊓ F k)) (N ⊓ F k) :=
            q_chain le_sup_right hB
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1)) (N ⊓ F k) := by rw [q_sup]
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1)) N := by
            rw [q_congr (F (k + 1)) (B := N ⊓ F k) (B' := N)]
            rw [inf_comm N, ← inf_assoc, inf_eq_left.mpr (hF k)]
  rw [key n, hn, q_zero bot_le, add_zero]

end Formalism.LatticeBaseChangeAlt
