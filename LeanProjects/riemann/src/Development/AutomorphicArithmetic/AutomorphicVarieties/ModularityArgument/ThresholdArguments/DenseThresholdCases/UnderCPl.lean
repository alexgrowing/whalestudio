import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.UnderCPl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
private theorem under_cPl {K : Type} [Field K] [NumberField K] [IsCMField K] (w : HeightOneSpectrum (𝓞 K)) :
    (cPl w).under (𝓞 ℚ) = w.under (𝓞 ℚ) := by
  have e : (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj K).toRingEquiv) :=
    (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  change x ∈ (cPl w).asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) ↔ x ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K))
  have e2 : RingOfIntegers.mapRingEquiv (IsCMField.complexConj K).toRingEquiv (algebraMap (𝓞 ℚ) (𝓞 K) x) =
      algebraMap (𝓞 ℚ) (𝓞 K) x :=
    RingOfIntegers.ext (map_ratCast (IsCMField.complexConj K) (x : ℚ))
  rw [e, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, e2]
theorem UpperTheory.V.Z.Bc.polarization_k_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → PolK := by
  intro hP K _ _ _ hK n hn l _ Ω _ _ _ _ _ ι r wt θ P hθ hd hC
  have h5 : NormGal := UpperTheory.galois_norm_compatibility_of_frobenius_restriction UpperTheory.frobenius_power_compatibility (UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility)
  have h8 : PolOfSat := UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse
  haveI : IsScalarTower ℚ (maximalRealSubfield K) Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  haveI : IsGalois ℚ K := inferInstance
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans ℚ K Ω⟩
  have hθ' : IsCycWt l (wt + ((n : ℤ) - 1))
      (θ.comp (res ℚ Ω (maximalRealSubfield K)) * cycBar (maximalRealSubfield K) Ω l ^ ((n : ℤ) - 1)) := by
    obtain ⟨M, χ, hM, hχ, rfl⟩ := hθ
    refine ⟨M, χ.comp (res ℚ Ω (maximalRealSubfield K)), hM, fun s hs => hχ _ hs, ?_⟩
    rw [zpow_add, mul_right_comm]
    rfl
  obtain ⟨hc, χ, art, a, ha⟩ := UpperTheory.exists_algebraic_heckeChar_cyclotomic hP.litN.aut.art _ Ω l ι _ _ hθ'
  have hL : IsLAdicCharOf ι χ _ := ⟨hc, art, a, ha⟩
  obtain ⟨χ', μ', hL', hN, hres, hs⟩ := UpperTheory.heckeChar_sign_fixed K Ω hK l ι χ _ hL n
  have hres' : μ'.comp (res (maximalRealSubfield K) Ω K) = θ.comp (res ℚ Ω K) * cycBar K Ω l ^ ((n : ℤ) - 1) :=
    hres.trans rfl
  refine ⟨χ', μ', ⟨hs, h8 hP.litN.aut.js.1 hP.litN.aut.gk K n hn P _ ?_⟩, hL', hres'⟩
  have hd' : DualTw (r.comp (res ℚ Ω K)) (θ.comp (res ℚ Ω K)) := let ⟨Q, hQ⟩ := hd; ⟨Q, fun s => hQ _⟩
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hI := UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic UpperTheory.frobenius_conj_of_galois_conjugate_places UpperTheory.hecke_eigenvalue_basic_properties ℚ K Ω l ι n r _ hC
  filter_upwards [h5 K Ω l ι χ' μ' hL', hI, hC.2, hl] with w ⟨hu, he⟩ h3 ⟨B₁, hB₁, hF⟩ hw
  obtain ⟨B, hB, hB'⟩ := h3 (cPl w) (under_cPl w)
  obtain rfl := hB.unique hB₁
  rw [hres'] at he
  exact ⟨hu, B, B, hB, hB', UpperTheory.frobenius_eigenvalues_dual K Ω l ι n _ _ hd' w hw B _ hF he⟩
end
