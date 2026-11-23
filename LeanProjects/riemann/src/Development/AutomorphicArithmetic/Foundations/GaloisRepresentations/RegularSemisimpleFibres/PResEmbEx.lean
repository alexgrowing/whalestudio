import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.DiscreteGroups.GlobalIrreducibility.DzGalKappa
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ResAlgClosed
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem res_algClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) :
    IsAlgClosed (IsLocalRing.ResidueField A) :=
  _root_.UpperTheory.Reformulated.B.Qk69.res_algClosed A

private theorem res_surj {Ω : Type} [Field Ω] [CharZero Ω] (hΩ : ∀ x : Ω, IsAlgebraic ℤ x) (A : ValuationSubring Ω) {κ : Type} [Field κ]
    [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (e : κ →+* IsLocalRing.ResidueField A) : Function.Surjective e := by
  letI := e.toAlgebra
  haveI : Algebra.IsIntegral κ (IsLocalRing.ResidueField A) := ⟨fun z => by
    obtain ⟨z', rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨P₀, h0, hP₀⟩ := hΩ (z' : Ω)
    have hP : aeval (z' : Ω) P₀.primPart = 0 := by
      have h1 := congrArg (aeval (z' : Ω)) P₀.eq_C_content_mul_primPart
      rw [hP₀, map_mul, aeval_C] at h1
      have h2 : algebraMap ℤ Ω P₀.content ≠ 0 := by
        simpa [Polynomial.content_eq_zero_iff] using h0
      exact (mul_eq_zero.1 h1.symm).resolve_left h2
    have hA : aeval z' P₀.primPart = 0 := by
      have h1 := aeval_algebraMap_apply Ω z' P₀.primPart
      change aeval (z' : Ω) _ = _ at h1
      rw [hP] at h1
      exact Subtype.val_injective h1.symm
    have hR : aeval (IsLocalRing.residue A z') P₀.primPart = 0 := by
      have h1 := aeval_algebraMap_apply (IsLocalRing.ResidueField A) z' P₀.primPart
      rw [hA, map_zero] at h1
      exact h1
    have hQ : P₀.primPart.map (algebraMap ℤ κ) ≠ 0 := by
      intro h
      have hdvd : C (p : ℤ) ∣ P₀.primPart := (C_dvd_iff_dvd_coeff _ _).2 fun n => by
        have h1 := congrArg (fun q => q.coeff n) h
        simp only [coeff_map, coeff_zero] at h1
        have h2 := congrArg e h1
        simp only [eq_intCast, map_intCast, map_zero] at h2
        exact (CharP.intCast_eq_zero_iff _ p _).1 h2
      exact (Nat.prime_iff_prime_int.1 Fact.out).not_unit (P₀.isPrimitive_primPart _ hdvd)
    refine IsAlgebraic.isIntegral ⟨_, hQ, ?_⟩
    rw [aeval_def, eval₂_map, Subsingleton.elim ((algebraMap κ (IsLocalRing.ResidueField A)).comp (algebraMap ℤ κ))
      (algebraMap ℤ (IsLocalRing.ResidueField A))]
    exact hR⟩
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := κ) (K := IsLocalRing.ResidueField A)).2

theorem UpperTheory.Gal.InertialTypesAlt.resEmbEx :
    ResEmbEx := by
  intro E Ω _ _ _ _ _ A v hv
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI := res_algClosed A
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A,
      ∀ x, e₀ (DiscreteGroups.sglob.DzType.kappaP v x) = DiscreteGroups.sglob.DzType.kappaQ A x := by
    refine ⟨RingHom.liftOfSurjective _ (DiscreteGroups.sglob.DzType.kappa_surj_O v) ⟨DiscreteGroups.sglob.DzType.kappaQ A, fun x hx => ?_⟩,
      fun x => ?_⟩
    · rw [DiscreteGroups.sglob.DzType.kappa_ker_O, ← DiscreteGroups.sglob.DzType.kappa_ker_A A v hv] at hx
      exact hx
    · exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists 𝓀[v.adicCompletion E]
  haveI : Fact p.Prime := ⟨CharP.char_is_prime 𝓀[v.adicCompletion E] p⟩
  haveI : CharP (IsLocalRing.ResidueField A) p := charP_of_injective_ringHom e₀.injective p
  letI := e₀.toAlgebra
  let e : AlgebraicClosure 𝓀[v.adicCompletion E] →ₐ[𝓀[v.adicCompletion E]] IsLocalRing.ResidueField A := IsAlgClosed.lift
  have hres : ResEmb A v (e : AlgebraicClosure 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A) := by
    intro x y z hy hz
    have h1 : IsLocalRing.residue 𝒪[v.adicCompletion E] y = DiscreteGroups.sglob.DzType.kappaP v x := by
      rw [DiscreteGroups.sglob.DzType.kappaP, RingHom.comp_apply]
      exact congrArg _ (Subtype.ext hy)
    have h2 : IsLocalRing.residue A z = DiscreteGroups.sglob.DzType.kappaQ A x := by
      rw [DiscreteGroups.sglob.DzType.kappaQ, RingHom.comp_apply]
      exact congrArg _ (Subtype.ext hz)
    rw [h1, h2, ← he₀]
    exact e.commutes _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hΩ : ∀ x : Ω, IsAlgebraic ℤ x := by
    haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
    exact fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  have hs := res_surj hΩ A p (e : AlgebraicClosure 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A)
  let e' := RingEquiv.ofBijective (e : AlgebraicClosure 𝓀[v.adicCompletion E] →+* IsLocalRing.ResidueField A)
    ⟨RingHom.injective _, hs⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField 𝓀[v.adicCompletion E]
  refine ⟨⟨_, hres⟩, θ.comp (e'.symm : IsLocalRing.ResidueField A →* _), fun x y hx hy h => ?_⟩
  exact e'.symm.injective (hθ _ _ (by simpa using hx) (by simpa using hy) h)
