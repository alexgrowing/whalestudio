import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnifVSpec

noncomputable section

namespace PI.VolStabS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨_, hE, _, hτ⟩ := hCM
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hτ, hτ, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    haveI := hE
    have hc := IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hc
    apply hc
    ext x
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← hτ, hall]
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv]
  abel

theorem anti_coeff (σ : E →ₐ[F] E) {δ : E} (hδ0 : δ ≠ 0) (hσδ : σ δ = -δ) (s t : F)
    (h : σ (s • (1 : E) + t • δ) = s • 1 + t • δ) : t = 0 := by
  simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, hσδ, mul_one] at h
  have h2 : (2 : E) * (algebraMap F E t * δ) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact (algebraMap F E).injective (by rw [h4, map_zero])
    · exact absurd h4 hδ0

theorem exists_basis_anti (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) :
    ∃ (δ : E) (D0 : F) (c : Module.Basis (Fin 2) F E), δ ≠ 0 ∧ σ δ = -δ ∧
      δ * δ = algebraMap F E D0 ∧ D0 ≠ 0 ∧ c 0 = 1 ∧ c 1 = δ := by
  obtain ⟨δ, hδ0, hσδ⟩ := exists_anti σ hCM
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      apply anti_coeff σ hδ0 hσδ s t
      rw [hst, map_zero]
    subst ht
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right one_ne_zero, rfl⟩
  let c := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hc : ⇑c = ![(1 : E), δ] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  obtain ⟨s, t, hst⟩ : ∃ s t : F, δ * δ = s • (1 : E) + t • δ := by
    have hsum := c.sum_repr (δ * δ)
    rw [Fin.sum_univ_two, hc] at hsum
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hsum
    exact ⟨_, _, hsum.symm⟩
  have ht : t = 0 := by
    apply anti_coeff σ hδ0 hσδ s t
    rw [← hst, map_mul, hσδ, neg_mul_neg]
  subst ht
  rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
  refine ⟨δ, s, c, hδ0, hσδ, hst, ?_, by simp [hc], by simp [hc]⟩
  rintro rfl
  rw [map_zero] at hst
  exact hδ0 (mul_self_eq_zero.mp hst)

end PI.VolStabS
