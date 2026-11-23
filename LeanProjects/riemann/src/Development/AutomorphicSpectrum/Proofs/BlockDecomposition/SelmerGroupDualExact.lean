import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GalDual

theorem contAction_twDual_of_continuous {R Γ M : Type*} [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [AddCommGroup M]
    [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (χ : Γ →* Rˣ)
    (hχ : Continuous χ) (ρ : Representation R Γ M) (hρ : ContAction ρ) :
    ContAction (twDual χ ρ) := by
  have key : ∀ φ : TDual R M, Continuous (fun g : Γ => twDual χ ρ g φ) := by
    intro φ
    rw [continuous_discrete_rng]
    intro ψ
    have hset : (fun g : Γ => twDual χ ρ g φ) ⁻¹' {ψ} =
        ⋂ m : M, (fun g : Γ => ((χ g : Rˣ) : R) * φ (ρ g⁻¹ m)) ⁻¹' {ψ m} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
      exact ⟨fun h m => by rw [← h]; rfl, fun h => TDual.ext h⟩
    rw [hset]
    refine isOpen_iInter_of_finite fun m => ?_
    have h1 : Continuous fun g : Γ => ρ g⁻¹ m :=
      Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) hρ
        (continuous_inv.prodMk continuous_const)
    have h2 : Continuous fun g : Γ => φ (ρ g⁻¹ m) :=
      (continuous_of_discreteTopology (f := fun x : M => φ x)).comp h1
    have h3 : Continuous fun g : Γ => ((χ g : Rˣ) : R) * φ (ρ g⁻¹ m) :=
      (Units.continuous_val.comp hχ).mul h2
    exact (isOpen_discrete {ψ m}).preimage h3
  exact continuous_prod_of_discrete_right.2 key

theorem contAction_twDual : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω)
    (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
    (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hρ : ContAction ρ), μ.comp (toGS Ω _) = cycMod F Ω l r → ContAction (twDual μ ρ) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ hμ
  have hc : Continuous μ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have : (μ ∘ QuotientGroup.mk : G F Ω → _) = cycMod F Ω l r := by rw [← hμ]; rfl
    rw [this]; exact continuous_cycMod
  exact contAction_twDual_of_continuous μ hc ρ hρ

end GlobalTheory.CompanionTheory.GalDual
