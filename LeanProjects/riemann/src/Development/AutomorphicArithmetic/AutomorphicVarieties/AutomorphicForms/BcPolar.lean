import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBC0
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusSignCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurTwistHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BaseChangeNoSelfTwistOfFrobeniusSignIrreducible
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BaseChangeAttachedOfFrobeniusRestriction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BaseChangeComplexConjInvariance
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IdeleNormLocalCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IdeleNormValuationOfLocalCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisNormCompatibilityOfFrobeniusRestriction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAlgebraicHeckeCharCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharSignFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolOfSatOfThetaSat

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

theorem UpperTheory.V.Af.Bc.bcPolar_of (hP : Hypotheses₂) (h1 : NoTwist) (h2 : Br.BcAtt0) (h3 : Br.BcConj0) (h4 : FrobDual) (h5 : NormGal)
    (h6 : CycHecke) (h7 : SignFix) (h8 : PolOfSat) (h9 : IrrBasic) : Br.BcPolarW := by
  intro K _ _ _ hK n _ hn l _ Ω _ _ _ _ _ ι r wt θ π hreg hr hatt hθ hd hirr
  obtain ⟨P, hBC⟩ := (Br.quadBCw hP ℚ K hK n hn π hreg).resolve_left fun ⟨η, hη, ht⟩ => h1 ℚ K Ω l ι hK n r π hr hatt hirr η hη ht
  have hC := (h2 ℚ K Ω l ι n r π P hBC.toIsBC0).2 hatt ((h9.1 _ Unit _ n _).2.1 hirr)
  haveI : IsScalarTower ℚ (maximalRealSubfield K) Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  have hθ' : IsCycWt l (wt + ((n : ℤ) - 1))
      (θ.comp (res ℚ Ω (maximalRealSubfield K)) * cycBar (maximalRealSubfield K) Ω l ^ ((n : ℤ) - 1)) := by
    obtain ⟨M, χ, hM, hχ, rfl⟩ := hθ
    refine ⟨M, χ.comp (res ℚ Ω (maximalRealSubfield K)), hM, fun s hs => hχ _ hs, ?_⟩
    rw [zpow_add, mul_right_comm]
    rfl
  obtain ⟨hc, χ, art, a, ha⟩ := h6 hP.litN.aut.art _ Ω l ι _ _ hθ'
  have hL : IsLAdicCharOf ι χ _ := ⟨hc, art, a, ha⟩
  obtain ⟨χ', μ', hL', hN, hres, hs⟩ := h7 K Ω hK l ι χ _ hL n
  have hres' : μ'.comp (res (maximalRealSubfield K) Ω K) = θ.comp (res ℚ Ω K) * cycBar K Ω l ^ ((n : ℤ) - 1) :=
    hres.trans rfl
  refine ⟨P, χ', μ', hBC, hC, ⟨hs, h8 hP.litN.aut.js.1 hP.litN.aut.gk K n hn P _ ?_⟩, hL', hres'⟩
  have hd' : DualTw (r.comp (res ℚ Ω K)) (θ.comp (res ℚ Ω K)) := let ⟨Q, hQ⟩ := hd; ⟨Q, fun s => hQ _⟩
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  filter_upwards [h5 K Ω l ι χ' μ' hL', h3 ℚ K n π P hBC.toIsBC0, hC.2, hl] with w ⟨hu, he⟩ ⟨B, hB, hB'⟩ ⟨B₁, hB₁, hF⟩ hw
  obtain rfl := hB.unique hB₁
  rw [hres'] at he
  exact ⟨hu, B, B, hB, hB', h4 K Ω l ι n _ _ hd' w hw B _ hF he⟩

theorem UpperTheory.V.Af.Bc.bcAtt : BcAtt := UpperTheory.baseChange_attached_of_frobenius_restriction UpperTheory.frobenius_power_compatibility

theorem UpperTheory.V.Af.Bc.irrBasic : IrrBasic := UpperTheory.galoisRep_irreducibility_criterion

theorem UpperTheory.V.Af.Bc.noTwist (hP : Hypotheses₂) : NoTwist :=
  UpperTheory.baseChange_noSelfTwist_of_frobenius_sign_irreducible (isoOfFrob hP) UpperTheory.frobenius_eigenvalues_twist UpperTheory.exists_quadratic_sign_character UpperTheory.frobenius_sign_compatibility UpperTheory.schur_twist_holds UpperTheory.galoisRep_irreducibility_criterion

theorem UpperTheory.V.Af.Bc.normGal : NormGal := UpperTheory.galois_norm_compatibility_of_frobenius_restriction UpperTheory.frobenius_power_compatibility (UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility)

theorem UpperTheory.V.Af.Bc.bcPolar (hP : Hypotheses₂) : Br.BcPolarW :=
  Bc.bcPolar_of hP (Bc.noTwist hP) Br.bcAtt0 Br.bcConj0 UpperTheory.frobenius_eigenvalues_dual Bc.normGal UpperTheory.exists_algebraic_heckeChar_cyclotomic UpperTheory.heckeChar_sign_fixed
    (UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse) Bc.irrBasic
