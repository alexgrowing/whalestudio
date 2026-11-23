import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcPtTail
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcGalIdx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

theorem UpperTheory.V.X.galTail :
    LocalFiniteness → GlobalFiniteness → GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {SP : Set (HeightOneSpectrum (𝓞 ℚ))} {T Q : Finset ℕ} (v0 : T) {pl : ℕ → ValuationSubring Ω} {K : Subgroup (G ℚ Ω)}, GalData l SP T Q pl K → ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k (GS Ω SP) M), ContAction ρ → finrank k (shaF (galFrame SP T Q v0 pl K) ρ) + ∑ v : T, finrank k (H2 (ρ.comp (locHom SP (pl v)))) + ∑ q : Q, finrank k (H2 (ρ.comp (locHom SP (pl q)))) = finrank k (H2 ρ) + finrank k (Loc.H0dual (cycK Ω l k) (ρ.comp (toGS Ω SP))) := by
  intro lf gf pt Ω _ _ _ l _ SP T Q v0 pl K hD k _ _ _ M _ _ _ _ _ ρ hρ
  obtain ⟨S, e, rfl, hl, hT, hQ⟩ := galIdx Ω l v0 hD
  let B : T ⊕ Q → ValuationSubring Ω := Sum.elim (fun v => pl v) (fun q => pl q)
  have hB : ∀ x, IsPlaceOver (B x) (e x).1 := by
    rintro (v | q)
    · exact hT v
    · exact hQ q
  have hA : ∀ v : S, IsPlaceOver (B (e.symm v)) v.1 := fun v => by
    have := hB (e.symm v)
    rwa [e.apply_symm_apply] at this
  have h := ptTail lf gf pt Ω l hD.l_odd S hl (fun v => B (e.symm v)) hA k M ρ hρ
  have hsum : ∑ v : S, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B (e.symm v))))) =
      ∑ v : T, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (pl v)))) +
        ∑ q : Q, finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (pl q)))) := by
    rw [e.symm.sum_comp (fun x => finrank k (H2 (ρ.comp (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B x))))),
      Fintype.sum_sum_type]
    rfl
  have hsha : Sha2 ρ (fun v => locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B (e.symm v)))
      (fun v => continuous_locHom _ (B (e.symm v))) = shaF (galFrame (S : Set (HeightOneSpectrum (𝓞 ℚ))) T Q v0 pl K) ρ := by
    have h1 := e.symm.iInf_comp (g := fun x => LinearMap.ker (resH2 ρ (locHom (S : Set (HeightOneSpectrum (𝓞 ℚ))) (B x)) (continuous_locHom _ (B x))))
    rw [iInf_sum] at h1
    exact h1
  rw [hsum, hsha, ← add_assoc] at h
  exact h
