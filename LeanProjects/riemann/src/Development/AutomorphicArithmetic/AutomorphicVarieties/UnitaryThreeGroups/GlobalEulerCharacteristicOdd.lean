import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GlobalCohomologyFiniteSet
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

theorem UpperTheory.global_euler_characteristic_odd :
    GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω), ContainsAbove S l → (∀ v, IsPlaceOver (A v) v.1) →
                   ∀ ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M, ContAction ρ → (∃ g : G ℚ Ω, cycMod ℚ Ω l 1 g = -1 ∧ ρ (toGS Ω _ g) = 1) →
                   ∀ x : ∀ v : S, H2 (ρ.comp ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).comp (Dec (F := ℚ) (A v)).subtype) : Representation k _ M), ∃ z : H2 ρ,
                     ∀ v, resH2 ρ ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).comp (Dec (F := ℚ) (A v)).subtype) ((continuous_toGS Ω _).comp continuous_subtype_val) z = x v := by
  intro hPT Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ _ _ hl S A hS hA ρ hρ hg x
  obtain ⟨g, hg1, hg2⟩ := hg
  haveI : Finite M := Module.finite_of_finite k
  have hp : l.Prime := Fact.out
  choose κ hκ using fun v => Submodule.Quotient.mk_surjective _ (x v)
  have hn : ((l - 1 : ℕ) : ZMod (l ^ 1)) = (cycMod ℚ Ω l 1 g : (ZMod (l ^ 1))ˣ) := by
    have h0 : ((l : ℕ) : ZMod (l ^ 1)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff, pow_one]
    rw [hg1, Nat.cast_sub hp.one_le, h0]
    simp
  have hne : (1 : k) ≠ ((l - 1 : ℕ) : k) := by
    rw [Nat.cast_sub hp.one_le, CharP.cast_eq_zero k l, Nat.cast_one]
    intro h
    have h2 : ((2 : ℕ) : k) = 0 := by
      push_cast
      linear_combination h
    rw [CharP.cast_eq_zero_iff k l] at h2
    exact hl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  obtain ⟨z, hz⟩ := UpperTheory.global_cohomology_finite_set hPT Ω l hl k M S A ρ hS hA hρ
    ⟨g, 1, l - 1, fun m => by rw [one_smul]; exact (congrArg (fun f : Module.End k M => f m) hg2), hn, hne⟩ κ
  refine ⟨Submodule.Quotient.mk z, fun v => ?_⟩
  rw [← hκ v]
  exact (Submodule.Quotient.eq _).2 (hz v)
