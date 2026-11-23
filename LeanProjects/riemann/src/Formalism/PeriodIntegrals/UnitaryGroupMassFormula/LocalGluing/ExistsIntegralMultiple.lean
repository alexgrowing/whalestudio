import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOfPair

noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.Glue

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem scale_E (L : LocE F E) (y : E) :
    ∃ r : 𝒪[F], (r : F) ≠ 0 ∧ algebraMap F E r * y ∈ L.O := by
  obtain ⟨T, hT⟩ := SlopeTestRemainingChoices.tr_ex L y
  obtain ⟨N, hN⟩ := SlopeTestRemainingChoices.nm_ex L y
  obtain ⟨r₁, h10, h1⟩ := SlopeTestRemainingChoices.exists_scale T
  obtain ⟨r₂, h20, h2⟩ := SlopeTestRemainingChoices.exists_scale N
  obtain ⟨r, hr⟩ : ∃ r : 𝒪[F], (r : F) = (r₁ : F) * (r₂ : F) := ⟨r₁ * r₂, rfl⟩
  refine ⟨r, by rw [hr]; exact mul_ne_zero h10 h20, ?_⟩
  refine SlopeTestRemainingChoices.mem_O_of_quad L _ ⟨(r : F) * T, ?_⟩ ⟨(r : F) * (r : F) * N, ?_⟩ ?_
  · have : (r : F) * T = (r₂ : F) * ((r₁ : F) * T) := by rw [hr]; ring
    rw [this]; exact (𝒪[F]).mul_mem r₂.2 h1
  · have : (r : F) * (r : F) * N = ((r₁ : F) * (r₁ : F) * (r₂ : F)) * ((r₂ : F) * N) := by
      rw [hr]; ring
    rw [this]; exact (𝒪[F]).mul_mem ((𝒪[F]).mul_mem ((𝒪[F]).mul_mem r₁.2 r₁.2) r₂.2) h2
  · simp only [map_mul, hT, hN]
    ring

end

theorem existsIntegralMultiple : Scale := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ S w hw
  have key : ∀ (r : 𝒪[F]) (v : V), v ∈ S → algebraMap F E r • v ∈ S := by
    intro r v hv
    have : (⟨algebraMap F E r, SlopeTestRemainingChoices.algebraMap_mem_O M.L r⟩ : M.L.O) • v ∈ S := S.smul_mem _ hv
    exact this
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, by simp, by simpa using hx⟩
  | zero => exact ⟨1, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr0, hr⟩ := hx
    obtain ⟨s, hs0, hs⟩ := hy
    obtain ⟨t, ht⟩ : ∃ t : 𝒪[F], (t : F) = (r : F) * (s : F) := ⟨r * s, rfl⟩
    refine ⟨t, by rw [ht]; exact mul_ne_zero hr0 hs0, ?_⟩
    have e : algebraMap F E t • (x + y) =
        algebraMap F E s • (algebraMap F E r • x) + algebraMap F E r • (algebraMap F E s • y) := by
      rw [ht, smul_add, smul_smul, smul_smul, map_mul, mul_comm (algebraMap F E s)]
    rw [e]
    exact S.add_mem (key s _ hr) (key r _ hs)
  | smul a x _ hx =>
    obtain ⟨r, hr0, hr⟩ := hx
    obtain ⟨s, hs0, hs⟩ := scale_E M.L a
    obtain ⟨t, ht⟩ : ∃ t : 𝒪[F], (t : F) = (s : F) * (r : F) := ⟨s * r, rfl⟩
    refine ⟨t, by rw [ht]; exact mul_ne_zero hs0 hr0, ?_⟩
    have e : algebraMap F E t • (a • x) =
        (⟨algebraMap F E s * a, hs⟩ : M.L.O) • (algebraMap F E r • x) := by
      change _ = (algebraMap F E s * a) • (algebraMap F E r • x)
      rw [ht, smul_smul, smul_smul, map_mul]
      ring_nf
    rw [e]
    exact S.smul_mem _ hr

end PI.LocHerm.Glue
