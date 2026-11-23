import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem cup_product_injective_comp {R Γ D M : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    [Group Γ] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (φ : D →* Γ)
    (hρ : ContAction (ρ.comp φ)) (χ' : D →* Rˣ) (e : χ' = χ.comp φ)
    (h : Function.Injective (cupH1H1TwistedDual χ' (ρ.comp φ) (MonoidHom.id D) (hρ.comp' continuous_id))) :
    Function.Injective (cupH1H1TwistedDual χ ρ φ hρ) := by
  subst e
  have e1 : (twDual χ ρ).comp φ = (twDual (χ.comp φ) (ρ.comp φ)).comp (MonoidHom.id D) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun y => TDual.ext fun m => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply, map_inv φ]
  have gen : ∀ (σ σ' : Representation R D (TDual R M)) (_ : σ = σ') h1 h2,
      Function.Injective (cupProductH1H1 σ' (ρ.comp φ) ((charRep χ).comp φ) evalPair.flip
        continuous_of_discreteTopology h2 hρ) →
      Function.Injective (cupProductH1H1 σ (ρ.comp φ) ((charRep χ).comp φ) evalPair.flip
        continuous_of_discreteTopology h1 hρ) := by
    intro σ σ' e h1 h2 h
    subst e
    exact h
  exact gen _ _ e1 _ (fun g y x => evalPair_equiv (χ.comp φ) (ρ.comp φ) g x y) h

theorem UpperTheory.V.Ws.dualSelmer_orthogonalComplement_conditions :
    LocalTateDuality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ 1))ˣ) (Av : S → ValuationSubring Ω), μ.comp (toGS Ω _) = cycMod F Ω l 1 → (∀ v, IsPlaceOver (Av v) v.1) → Sel (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) fun _ => ⊤) = Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) := by
  intro hT F Ω _ _ _ _ _ l _ M _ _ _ _ _ S ρ hρ μ Av hμ hA
  have key : ∀ v : S, Function.Injective
      (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))) := fun v => by
    have h := (hT F Ω l 1 M (Av v) (ρ.comp (locFam S Av v)) v.1 one_pos (hA v)
      (hρ.comp' (continuous_locFam S Av v))).2.2.1.1
    exact cup_product_injective_comp μ ρ _ _ _ (by rw [← hμ]; rfl) h
  ext y
  rw [mem_Sel, Sha1, Submodule.mem_iInf]
  refine forall_congr' fun v => ?_
  rw [mem_perpCond, LinearMap.mem_ker]
  constructor
  · intro h
    apply key v
    rw [map_zero]
    exact LinearMap.ext fun x => h x trivial
  · intro h x _
    rw [h, map_zero, LinearMap.zero_apply]
