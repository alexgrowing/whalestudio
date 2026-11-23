import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem UpperTheory.V.CA.cmquot_of_finite {P R : Type} [CommRing P] [IsLocalRing P] [CommRing R]
    [IsLocalRing R] (hP : IsCM P) (φ : P →+* R) (hf : φ.Finite) [IsLocalHom φ] : IsCMQuot R := by
  letI := φ.toAlgebra
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf.finiteType
  let N : Ideal (MvPolynomial (Fin n) P) := Ideal.comap g.toRingHom (maximalIdeal R)
  haveI : N.IsMaximal := Ideal.comap_isMaximal_of_surjective g.toRingHom hg
  have hgC : g.toRingHom.comp MvPolynomial.C = φ := by
    refine RingHom.ext fun x => ?_
    show g (MvPolynomial.C x) = φ x
    rw [← MvPolynomial.algebraMap_eq, g.commutes]
    rfl
  have hC : Ideal.comap MvPolynomial.C N = maximalIdeal P := by
    have h := congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint φ)
    show Ideal.comap MvPolynomial.C (Ideal.comap g.toRingHom (maximalIdeal R)) = maximalIdeal P
    rw [Ideal.comap_comap, hgC]
    exact h
  obtain ⟨hcm, -⟩ := isCM_localization_mvPolynomial hP n N hC
  have hu : ∀ y : N.primeCompl, IsUnit (g.toRingHom y) := fun y =>
    IsLocalRing.notMem_maximalIdeal.mp y.2
  refine ⟨Localization.AtPrime N, inferInstance, inferInstance, IsLocalization.lift hu, hcm, ?_⟩
  intro r
  obtain ⟨p, rfl⟩ := hg r
  exact ⟨algebraMap _ _ p, IsLocalization.lift_eq hu p⟩

theorem UpperTheory.V.CA.cl_cmquot :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R], IsCL O R → IsCMQuot R := by
  intro O _ _ _ _ R _ _ _ hR
  haveI := hR.noeth
  obtain ⟨n, a, ha⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian (maximalIdeal R))
  have hspan : Ideal.span (Set.range a) = maximalIdeal R := ha
  have hmem : ∀ s, a s ∈ maximalIdeal R := by
    intro s
    rw [← hspan]
    exact Ideal.subset_span ⟨s, rfl⟩
  have hrad : maximalIdeal R ≤
      (Ideal.span (Set.range a) ⊔ Ideal.map (algebraMap O R) (maximalIdeal O)).radical := by
    rw [hspan]
    exact le_sup_left.trans Ideal.le_radical
  obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps O R hR (Fin n) a hmem hrad
  haveI := hloc
  exact cmquot_of_finite (cl_cm.1 O n).1 φ hfin
