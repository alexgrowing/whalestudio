import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFL

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Polynomial
open ValuativeRel

theorem fl_hensel {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    (hl : IsNonarchimedeanLocalField F) : HenselianRing 𝒪[F] 𝓂[F] := by
  haveI := hl
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  exact IsAdicComplete.henselianRing _ _

theorem fl_coe_mul {F : Type} [Field F] [ValuativeRel F] (a b : 𝒪[F]) :
    ((a * b : 𝒪[F]) : F) = (a : F) * b := rfl

theorem fl_sq_div {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (b n : 𝒪[F]) (hbn : b * b = n) (hn : n ∈ 𝓂[F]) :
    ∃ z ∈ L.O, algebraMap F E b = algebraMap F E ϖ * z := by
  haveI := hl
  have hb : b ∈ 𝓂[F] := by
    have h2 : b * b ∈ 𝓂[F] := hbn ▸ hn
    rcases (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).isPrime.mem_or_mem h2 with h | h <;> exact h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  exact ⟨algebraMap F E c, fl_int_mem L c, by rw [fl_coe_mul, map_mul]⟩

theorem fl_local {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hinj : Function.Injective (algebraMap F E))
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    ∀ x ∈ L.O, (¬ ∃ z ∈ L.O, x = algebraMap F E ϖ * z) → ∃ y ∈ L.O, x * y = 1 := by
  intro x hx hnd
  haveI := hl
  obtain ⟨n, hn⟩ := fl_norm L hinj hx
  obtain ⟨t, ht⟩ := fl_trace L hinj hx
  have hquad : x * x = algebraMap F E t * x - algebraMap F E n := by
    rw [ht, hn]; ring
  by_cases hnu : IsUnit n
  · obtain ⟨u, rfl⟩ := hnu
    refine ⟨L.cj x * algebraMap F E ((↑u⁻¹ : 𝒪[F]) : F), mul_mem (fl_cj_mem L hx) (fl_int_mem L _), ?_⟩
    rw [← mul_assoc, ← hn, ← map_mul, ← fl_coe_mul, Units.mul_inv]
    simp
  · exfalso
    have hnm : n ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal n).2 hnu
    have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    by_cases htm : t ∈ 𝓂[F]
    · apply hnd
      rw [hspan, Ideal.mem_span_singleton] at htm hnm
      obtain ⟨t', rfl⟩ := htm
      obtain ⟨n', rfl⟩ := hnm
      have hsp : x * x ∈ Submodule.span L.O {algebraMap F E ϖ} := by
        refine Submodule.mem_span_singleton.2 ⟨⟨algebraMap F E t' * x - algebraMap F E n',
          sub_mem (mul_mem (fl_int_mem L t') hx) (fl_int_mem L n')⟩, ?_⟩
        rw [hquad, fl_coe_mul, fl_coe_mul, map_mul, map_mul]
        show (algebraMap F E t' * x - algebraMap F E n') * algebraMap F E ϖ = _
        ring
      obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 (L.unram ϖ hϖ x hx hsp)
      exact ⟨z, z.2, by rw [← hz, Subring.smul_def]; exact mul_comm _ _⟩
    · haveI := fl_hensel hl
      haveI := IsLocalRing.maximalIdeal.isMaximal 𝒪[F]
      let f : Polynomial 𝒪[F] := X ^ 2 + (C n - C t * X)
      have hf : f.Monic := by
        refine (monic_X_pow 2).add_of_left ?_
        rw [degree_X_pow]
        refine lt_of_le_of_lt (degree_sub_le _ _) ?_
        exact max_lt (lt_of_le_of_lt degree_C_le (by norm_num))
          (lt_of_le_of_lt (degree_C_mul_X_le t) (by norm_num))
      have h0 : f.eval 0 ∈ 𝓂[F] := by simpa [f] using hnm
      have h1 : IsUnit (Ideal.Quotient.mk 𝓂[F] (f.derivative.eval 0)) := by
        letI := Ideal.Quotient.field 𝓂[F]
        have hne : Ideal.Quotient.mk 𝓂[F] (f.derivative.eval 0) ≠ 0 := by
          rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
          simpa [f, Polynomial.derivative_sub, Polynomial.derivative_mul] using htm
        exact hne.isUnit
      obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian f hf 0 h0 h1
      have hroot : a ^ 2 + (n - t * a) = 0 := by simpa [f, Polynomial.IsRoot] using ha
      have hrootE : algebraMap F E (a : F) ^ 2 + (algebraMap F E (n : F) -
          algebraMap F E (t : F) * algebraMap F E (a : F)) = 0 := by
        have := congrArg (fun r : 𝒪[F] => algebraMap F E (r : F)) hroot
        simpa [map_sub, map_mul, map_pow, map_add] using this
      have hfac : (x - algebraMap F E (a : F)) * (x - (algebraMap F E (t : F) - algebraMap F E (a : F))) = 0 := by
        linear_combination hquad - hrootE
      have hxF : ∃ b : 𝒪[F], x = algebraMap F E (b : F) := by
        by_cases hxa : x - algebraMap F E (a : F) = 0
        · exact ⟨a, sub_eq_zero.1 hxa⟩
        · obtain ⟨u, hu⟩ := hE _ hxa
          have : x - (algebraMap F E (t : F) - algebraMap F E (a : F)) = 0 := by
            have h2 := congrArg (fun y => (↑u⁻¹ : E) * y) hfac
            simp only [mul_zero] at h2
            rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h2
            exact h2
          refine ⟨t - a, ?_⟩
          rw [sub_eq_zero.1 this]
          simp
      obtain ⟨b, rfl⟩ := hxF
      have hcj : L.cj (algebraMap F E (b : F)) = algebraMap F E (b : F) := L.cj.commutes _
      rw [hcj, ← map_mul, ← fl_coe_mul] at hn
      have hbn : b * b = n := Subtype.val_injective (hinj hn).symm
      exact hnd (fl_sq_div L hl ϖ hϖ b n hbn hnm)

end PI.UnitaryGroupMassFormula.CntFormula
