import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLowUni
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.NmUnfCol

theorem continuous_pFin (E : Type) [Field E] [NumberField E] : Continuous (pFin E) := by
  unfold pFin; exact continuous_snd

theorem col_inv_mul {E : Type} [Field E] [NumberField E] {a : ℕ}
    (u p : GA E (a + 1)) (hu : u ∈ GlobalTheory.JSW.NA E (a + 1)) (l : Fin (a + 1)) :
    ((p⁻¹ : GA E (a + 1)) : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) l 0 =
      (((u⁻¹ * p)⁻¹ : GA E (a + 1)) : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) l 0 := by
  have e : ((u⁻¹ * p)⁻¹ : GA E (a + 1)) = p⁻¹ * u := by group
  rw [e, Units.val_mul, Matrix.mul_apply]
  have hcol : ∀ j : Fin (a + 1), (u : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) j 0 = if j = 0 then 1 else 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj; simp [hu.2 0]
    · rw [if_neg hj]; exact hu.1 j 0 (Fin.pos_iff_ne_zero.2 hj)
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem finite_first_col_inv_compact : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (r + 1), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := by
  intro E _ _ r b₁ ⟨C, hC, hsupp⟩
  let f : GA E (r + 1) → (Fin (r + 1) → Af E) :=
    fun c l => pFin E (((c⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)
  have hf : Continuous f := by
    refine continuous_pi fun l => (continuous_pFin E).comp ?_
    have h0 : Continuous (fun c : GA E (r + 1) => ((c⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) :=
      Units.continuous_coe_inv
    exact (continuous_apply 0).comp ((continuous_apply l).comp h0)
  refine ⟨f '' C, hC.image hf, fun p hp => ?_⟩
  obtain ⟨u, hu, huC⟩ := hsupp p hp
  refine ⟨u⁻¹ * p, huC, funext fun l => ?_⟩
  simp only [f]
  rw [col_inv_mul u p hu l]

end GlobalTheory.NmUnfCol
