import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealInducedCharacters.Induced
open GlobalTheory.Published

noncomputable section

namespace GlobalTheory.InertiaEigenvalues

open BrauerSchur

theorem exists_transversal_index {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ∃ t : Fin H.index → G, (∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) ∧ ∀ x, ∃ i, (t i)⁻¹ * x ∈ H := by
  classical
  let e : G ⧸ H ≃ Fin H.index := Finite.equivFin (G ⧸ H)
  refine ⟨fun i => (e.symm i).out, fun i j => ?_, fun x => ⟨e (x : G ⧸ H), ?_⟩⟩
  · rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq', e.symm.injective.eq_iff]
  · rw [← QuotientGroup.eq]
    simp only [Equiv.symm_apply_apply, QuotientGroup.out_eq']

theorem inducedRep_cyclic_trace (G : Type) [Group G] [Fintype G] (H : Subgroup G) (χ : H →* ℂˣ) :
    ∃ (R : Representation ℂ G (Fin H.index → ℂ)) (v : Fin H.index → ℂ),
      (∀ σ : H, R σ v = (χ σ : ℂ) • v) ∧ Submodule.span ℂ (Set.range fun g => R g v) = ⊤ ∧
      ∀ g, LinearMap.trace ℂ (Fin H.index → ℂ) (R g) = GlobalTheory.Published.indFun H (fun x => (χ x : ℂ)) g := by
  classical
  obtain ⟨t, ht, hc⟩ := exists_transversal_index H
  obtain ⟨i0, hi0⟩ := hc 1
  rw [mul_one] at hi0
  have hti0 : t i0 ∈ H := by simpa using H.inv_mem hi0
  have memiff : ∀ (k i : Fin H.index) (a : G), (t i)⁻¹ * a ∈ H → ((t k)⁻¹ * a * t i0 ∈ H ↔ k = i) := by
    intro k i a ha
    rw [← ht k i]
    constructor
    · intro hm
      have e : (t k)⁻¹ * t i = ((t k)⁻¹ * a * t i0) * (t i0)⁻¹ * ((t i)⁻¹ * a)⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hm (H.inv_mem hti0)) (H.inv_mem ha)
    · intro hm
      have e : (t k)⁻¹ * a * t i0 = ((t k)⁻¹ * t i) * ((t i)⁻¹ * a) * t i0 := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hm ha) hti0
  refine ⟨indRep H χ t ht hc, Pi.single i0 1, ?_, ?_, ?_⟩
  · intro σ
    ext k
    show Matrix.toLin' (indMat H χ t (σ : G)) (Pi.single i0 1) k = _
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    simp only [Matrix.col_apply, indMat, Pi.smul_apply, smul_eq_mul]
    have hσ : (t i0)⁻¹ * (σ : G) ∈ H := H.mul_mem hi0 σ.2
    by_cases hk : k = i0
    · subst hk
      rw [Pi.single_eq_same, mul_one, dot_conj H χ hti0 (σ : G)]
      unfold dot
      rw [dif_pos σ.2]
    · rw [Pi.single_eq_of_ne hk, mul_zero]
      unfold dot
      rw [dif_neg]
      rw [memiff k i0 _ hσ]
      exact hk
  · rw [eq_top_iff]
    have hsingle : ∀ i, Pi.single i (1 : ℂ) ∈ Submodule.span ℂ (Set.range fun g => indRep H χ t ht hc g (Pi.single i0 1)) := by
      intro i
      have hti : (t i)⁻¹ * t i ∈ H := by simpa using H.one_mem
      have hval : indRep H χ t ht hc (t i) (Pi.single i0 1) = dot H χ (t i0) • Pi.single i (1 : ℂ) := by
        ext k
        show Matrix.toLin' (indMat H χ t (t i)) (Pi.single i0 1) k = _
        rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
        simp only [Matrix.col_apply, indMat, Pi.smul_apply, smul_eq_mul]
        by_cases hk : k = i
        · subst hk
          rw [Pi.single_eq_same, mul_one, inv_mul_cancel, one_mul]
        · rw [Pi.single_eq_of_ne hk, mul_zero]
          unfold dot
          rw [dif_neg]
          rw [memiff k i _ hti]
          exact hk
      have hne : dot H χ (t i0) ≠ 0 := by
        unfold dot
        rw [dif_pos hti0]
        exact Units.ne_zero _
      have : Pi.single i (1 : ℂ) = (dot H χ (t i0))⁻¹ • indRep H χ t ht hc (t i) (Pi.single i0 1) := by
        rw [hval, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t i, rfl⟩)
    intro x _
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have e : (fun j => if i = j then (1 : ℂ) else 0) = Pi.single i 1 := by
      ext j; simp [Pi.single_apply, eq_comm]
    rw [e]; exact hsingle i
  · intro g
    rw [indRep_trace, ← indFun_eq_sum H χ t ht hc g]
    rfl

end GlobalTheory.InertiaEigenvalues

end
