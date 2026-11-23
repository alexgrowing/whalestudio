import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.Transport
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CohomologicalDimensionTopologicalIsoStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermFrameKTypeCoefficientsStatement

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GFParts

theorem card_eq_pow_of_torsion {V : Type} [AddCommGroup V] [Finite V] (l : ℕ) [Fact l.Prime] (r : ℕ)
    (h : ∀ a : V, (l ^ r) • a = 0) : ∃ k : ℕ, Nat.card V = l ^ k := by
  have hp : IsPGroup l (Multiplicative V) := fun g => ⟨r, by
    change Multiplicative.ofAdd ((l ^ r) • Multiplicative.toAdd g) = 1
    rw [h]; rfl⟩
  have : Finite (Multiplicative V) := inferInstanceAs (Finite V)
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  exact ⟨k, hk⟩

theorem mem_of_pow_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (l k : ℕ)
    (h : ((l ^ k : ℕ) : 𝓞 F) ∈ v.asIdeal) : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [Nat.cast_pow] at h
  exact v.isPrime.mem_of_pow_mem k h

theorem finite_H2_torsion_module : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))))) [IsDiscreteRep A], Finite A.V → (∀ a : A.V, (l ^ r) • a = 0) → Finite (cohomology A 2) := by
  intro F Ω _ _ _ _ _ l _ r S hS A _ hAf hAk
  obtain ⟨K, S', hS', ⟨θ⟩⟩ := GlobalTheory.T.galois_unramified_outside_descends_finite F Ω l S hS
  obtain ⟨k, hk⟩ := card_eq_pow_of_torsion l r hAk
  have hK : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card A.V : ℕ) : 𝓞 K.1) ∈ v.asIdeal →
      v ∈ (S' : Set (HeightOneSpectrum (𝓞 K.1))) := by
    intro v hv
    rw [hk] at hv
    exact Finset.mem_coe.2 (hS' v (mem_of_pow_mem v l k hv))
  refine PositivityTheory.Lit1.GFTransport.finite_cohomology_transport θ A 2 ?_
  let φ : galUnramifiedOutside K.1 (AlgebraicClosure ℚ) (S' : Set (HeightOneSpectrum (𝓞 K.1))) →*
      galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) :=
    (θ.symm : galUnramifiedOutside K.1 (AlgebraicClosure ℚ) (S' : Set (HeightOneSpectrum (𝓞 K.1))) ≃*
      galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))).toMonoidHom
  have : IsDiscreteRep (Rep.res φ A) := IsDiscreteRep.res (φ := φ) θ.symm.continuous A
  have : Finite (Rep.res φ A).V := hAf
  exact finite_cohomology_gs K (S' : Set (HeightOneSpectrum (𝓞 K.1))) (Rep.res φ A) hK 2 (by norm_num)

theorem cdp_gal_le_two (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ContainsAbove S l) (hl2 : l ≠ 2) :
    cdp l (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))) ≤ 2 := by
  obtain ⟨K, S', hS', ⟨e⟩⟩ := GlobalTheory.T.galois_unramified_outside_descends_finite F Ω l S hS
  rw [GlobalTheory.T.cohomological_dimension_topological_iso _ _ l e]
  exact cdp_galUnramifiedOutside_le_two K (S' : Set (HeightOneSpectrum (𝓞 K.1))) Fact.out
    (fun v hv => hS' v hv) (Or.inl hl2)

theorem subsingleton_hn : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → l ≠ 2 → ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))))) [IsDiscreteRep A], Finite A.V → (∀ a : A.V, (l ^ r) • a = 0) → ∀ n : ℕ, 3 ≤ n → Subsingleton (cohomology A n) := by
  intro F Ω _ _ _ _ _ l _ r S hS hl2 A _ _ hA n hn
  have hp : l.Prime := Fact.out
  have hcd := cdp_gal_le_two F Ω l S hS hl2
  refine subsingleton_cohomology_of_cdp_le_two (n := l ^ r) (pow_ne_zero r hp.ne_zero)
    (fun q hq hqd => ?_) A hA hn
  have hql : q = l := (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)
  subst hql
  exact hcd

end PositivityTheory.Lit1.GFParts
