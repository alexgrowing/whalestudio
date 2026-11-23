import Development.AutomorphicArithmetic.WhittakerHecke.LocalArtinInertiaValuationOfUniformizerPrime
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.tameRecAll :
    ∀ (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (g : ℕ) [Fact g.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A v), ((g : ℕ) : 𝓞 M) ∈ v.asIdeal → ((g : ℕ) : 𝓞 M) ∉ v.asIdeal ^ 2 → ∀ a : Weil h →* (v.adicCompletion M)ˣ, IsLocalArtin h a → ∀ π : Ω, π ^ (normV v - 1) = (g : Ω) → ∀ (t : Ine (F := M) A) (x : 𝓞 M), Valued.v ((a (ineIncl h t) : v.adicCompletion M) - algebraMap M (v.adicCompletion M) (x : M)) < 1 → A.valuation ((t : G M Ω) π / π - algebraMap M Ω (x : M)) < 1 :=
  UpperTheory.localArtin_inertia_valuation_of_uniformizer_prime
