import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCohomologyLocalGlobalDual
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoitouTateEulerCharacteristic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelmerGroupDualExact

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GaloisCoh

theorem finite_of_finite_ker {R A B : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Finite B] (f : A →ₗ[R] B)
    (hk : Finite (LinearMap.ker f)) : Finite A := by
  classical
  let s : B → A := fun b => if h : ∃ a, f a = b then h.choose else 0
  have hs : ∀ a, f (s (f a)) = f a := fun a => by
    have h : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp only [s, dif_pos h]
    exact h.choose_spec
  let φ : A → B × LinearMap.ker f := fun a =>
    (f a, ⟨a - s (f a), by simp [LinearMap.mem_ker, hs]⟩)
  refine Finite.of_injective φ fun a b hab => ?_
  have h1 : f a = f b := congrArg Prod.fst hab
  have h2 : a - s (f a) = b - s (f b) := congrArg (fun x => (x.2 : A)) hab
  rw [h1] at h2
  exact sub_left_injective h2

theorem global_finite_of_poitouTate : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), μ.comp (toGS Ω _) = cycMod F Ω l r → Finite (TDual (ZMod (l ^ r)) M) → LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → NineTermExact S Av μ j ρ hρ → ShaDual S Av μ ρ → Finite (H0 ρ) ∧ Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Finite (H0 (twDual μ ρ)) ∧ Finite (H1 (twDual μ ρ)) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ j hμ hT hF hr hA _ hSha
  have hρ' : ContAction (twDual μ ρ) := GlobalTheory.CompanionTheory.GalDual.contAction_twDual F Ω l r M S Av μ ρ hρ hμ
  obtain ⟨-, hS1, hS2⟩ := selmer_sha_eq_comap_ker F Ω l r M S Av μ ρ hρ
  obtain ⟨-, hT1, -⟩ := selmer_sha_eq_comap_ker F Ω l r (TDual (ZMod (l ^ r)) M) S Av μ
    (twDual μ ρ) hρ'
  have hloc := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r M S Av μ ρ hρ hF hr hA
  have hlocT := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r (TDual (ZMod (l ^ r)) M)
    S Av μ (twDual μ ρ) hρ' hF hr hA
  have p1 : Finite (∀ v : S, H1 (ρ.comp (locFam S Av v))) :=
    haveI := fun v => (hloc v).2.1
    inferInstance
  have p2 : Finite (∀ v : S, H2 (ρ.comp (locFam S Av v))) :=
    haveI := fun v => (hloc v).2.2
    inferInstance
  have pT : Finite (∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v))) :=
    haveI := fun v => (hlocT v).2.1
    inferInstance
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact inferInstance
  · refine finite_of_finite_ker (loc1 S Av ρ) ?_
    rw [← hS1]
    exact hSha.2.1
  · refine finite_of_finite_ker (loc2 S Av ρ) ?_
    rw [← hS2]
    exact hSha.1.2.1
  · exact inferInstance
  · refine finite_of_finite_ker (loc1 S Av (twDual μ ρ)) ?_
    rw [← hT1]
    exact hSha.1.1

end GlobalTheory.CompanionTheory.GaloisCoh

end
