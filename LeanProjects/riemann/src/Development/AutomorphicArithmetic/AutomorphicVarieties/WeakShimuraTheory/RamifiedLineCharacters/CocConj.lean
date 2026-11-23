import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cocConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ∀ c ∈ Z1 ρ, ∀ (v : HeightOneSpectrum (𝓞 F)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v →
      ((∃ m, ∀ g ∈ Dec (F := F) A, c g = ρ g m - m) → ∃ m, ∀ g ∈ Dec (F := F) A', c g = ρ g m - m) ∧
      ((∀ g ∈ Ine (F := F) A, ρ g = 1 ∧ c g = 0) → ∀ g ∈ Ine (F := F) A', c g = 0) := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ ρ c hc v A A' hA hA'
  obtain ⟨-, hco⟩ := hc
  obtain ⟨s, hs⟩ := exists_smul_eq_of_isPlaceOver hA hA'
  have h1 : c 1 = 0 := by simpa using hco 1 1
  have hinv : ρ s (c s⁻¹) = - c s := by
    have h := hco s s⁻¹
    rw [mul_inv_cancel, h1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  have hconj : ∀ g ∈ Dec (F := F) A', s⁻¹ * g * s ∈ Dec (F := F) A := by
    intro g hg
    rw [mem_Dec] at hg ⊢
    open scoped Pointwise in
    rw [mul_smul, mul_smul, hs, hg, ← hs, inv_smul_smul]
  refine ⟨?_, ?_⟩
  · rintro ⟨m, hm⟩
    refine ⟨ρ s m - c s, fun g hg => ?_⟩
    have hg' := hconj g hg
    have e2 : c (g * s) = c s + ρ s (c (s⁻¹ * g * s)) := by
      rw [← hco]
      congr 1
      group
    have e3 : c g = c (g * s) + ρ (g * s) (c s⁻¹) := by
      rw [← hco]
      congr 1
      group
    have e4 : ρ s (ρ (s⁻¹ * g * s) m) = ρ g (ρ s m) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [e3, e2, map_mul ρ g s, Module.End.mul_apply, hinv, hm _ hg']
    simp only [map_sub, map_neg]
    rw [e4]
    abel
  · intro hI g hg
    rw [← hs] at hg
    obtain ⟨hρ, hc0⟩ := hI _ (GlobalTheory.Cut.ShaBound.conj_mem_Ine' hg)
    have e2 : c (g * s) = c s + ρ s (c (s⁻¹ * g * s)) := by
      rw [← hco]
      congr 1
      group
    have e3 : c g = c (g * s) + ρ (g * s) (c s⁻¹) := by
      rw [← hco]
      congr 1
      group
    have hρg : ρ g = 1 := by
      have hgs : g = s * (s⁻¹ * g * s) * s⁻¹ := by group
      rw [hgs, map_mul, map_mul, hρ, mul_one, ← map_mul, mul_inv_cancel, map_one]
    rw [e3, e2, hc0, map_zero, add_zero, map_mul ρ g s, hρg, one_mul, hinv, add_neg_cancel]
