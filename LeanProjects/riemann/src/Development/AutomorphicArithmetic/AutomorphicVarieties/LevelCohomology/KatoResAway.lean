import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

theorem UpperTheory.V.X.Kato.resAway :
    ∀ (l : ℕ) [Fact l.Prime] (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (C V : Type) [CommRing C] [AddCommGroup V] [Module C V] (ρ : Representation C (G ℚ Ω) V) (c : G ℚ Ω → V), (∀ g h, c (g * h) = c g + ρ g (c h)) → (∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ x : V, ∀ s ∈ Ine (F := ℚ) A, c s = ρ s x - x) → ∀ w : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ x : V, ∀ s ∈ Ine (F := K) A, c (s.restrictScalars ℚ) = ρ (s.restrictScalars ℚ) x - x := by
  intro l _ K Ω _ _ _ _ _ _ _ C V _ _ _ ρ c hc hyp w hw
  haveI : IsAlgClosure ℚ Ω := IsAlgClosure.ofAlgebraic ℚ K Ω
  obtain ⟨B, hB⟩ := exists_isPlaceOver (F := K) Ω w
  have hne : w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hy0 hy (Algebra.IsIntegral.isIntegral y)
  let p : HeightOneSpectrum (𝓞 ℚ) := ⟨w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)), Ideal.comap_isPrime _ _, hne⟩
  have hBp : IsPlaceOver B p := by
    intro y
    have key := hB (algebraMap (𝓞 ℚ) (𝓞 K) y)
    have hcoe : ((algebraMap (𝓞 ℚ) (𝓞 K) y : 𝓞 K) : K) = algebraMap ℚ K (y : ℚ) := rfl
    rw [hcoe, ← IsScalarTower.algebraMap_apply] at key
    exact key
  have hlp : ((l : ℕ) : 𝓞 ℚ) ∉ p.asIdeal := by
    show _ ∉ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  obtain ⟨A, hA, x, hx⟩ := hyp p hlp
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hBp
  refine ⟨B, hB, ρ σ x - c σ, ?_⟩
  intro s hs
  have ht : s.restrictScalars ℚ ∈ Ine (F := ℚ) B := ⟨hs.1, fun y hy => hs.2 y hy⟩
  rw [← hσ] at ht
  have hu := hx _ (GlobalTheory.Cut.ShaBound.conj_mem_Ine' ht)
  have htu : s.restrictScalars ℚ * σ = σ * (σ⁻¹ * s.restrictScalars ℚ * σ) := by group
  have e1 := hc (s.restrictScalars ℚ) σ
  have e2 := hc σ (σ⁻¹ * s.restrictScalars ℚ * σ)
  rw [htu] at e1
  have hct := eq_sub_of_add_eq (e1.symm.trans e2)
  have hm : ρ σ (ρ (σ⁻¹ * s.restrictScalars ℚ * σ) x) = ρ (s.restrictScalars ℚ) (ρ σ x) := by
    rw [← Module.End.mul_apply, ← map_mul, ← htu, map_mul, Module.End.mul_apply]
  rw [hct, hu, map_sub, hm, map_sub]
  abel
