import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGramFibreOfHaar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNiceLocalFieldProductRingInfiniteAdelesComplet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticUnitaryLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitPropsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProdStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureSmulFactorsEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTupleMeasureExtOfPureTensorIntegralsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualHaarMeasureInfiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualMeasureGlobalConstRankOnlyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlaceStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.XbetaScale

theorem continuous_qR {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem units_inf (F : Type) [Field F] [NumberField F] :
    {c : Ainf F | ∀ w, c w ≠ 0} = {c | IsUnit c} := by
  ext c
  simp only [Set.mem_setOf_eq]
  refine Iff.trans ?_ (Pi.isUnit_iff (x := c)).symm
  simp only [isUnit_iff_ne_zero]

theorem units_fv (K : Type) [Field K] : {c : K | c ≠ 0} = {c | IsUnit c} := by
  ext c
  simp only [Set.mem_setOf_eq, isUnit_iff_ne_zero]

theorem fib_eq_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (hR : Nice R) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E))
    (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) (r t : ℝ≥0) (ht : t ≠ 0)
    (hν : (t • ν).IsAddHaarMeasure) (hβ : IsUnit β) (hm : FibAt R σ J μ ν β m)
    (fib : R → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsFibreFamily (r • μ) (fun X => qR R σ J (X 0)) id Set.univ (t • ν) {c | IsUnit c} fib) :
    fib β = (r / t) • m := by
  obtain ⟨fib0, h0, rfl⟩ := hm
  exact (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ R hR M J (r • μ) (t • ν) β _ hν hβ
    ⟨_, GlobalTheory.GramFibreRescale.isFibreFamily_smul h0 r t ht, rfl⟩).2.2 _ ⟨fib, hfib, rfl⟩

end GlobalTheory.GaugeEx.XbetaScale

namespace GlobalTheory.GaugeEx

open XbetaScale

theorem isXbetaMeasure_iff_smul_std : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∃ κ : ℕ → ℝ≥0, (∀ M, κ M ≠ 0) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F) (ψ : AddChar (AF F) ℂ) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), 1 ≤ M → IsHermND σ J → β ≠ 0 → IsCharAF F ψ → IsStdX s σ J β ν → ∀ νX, IsXbetaMeasure F E σ M J ψ β νX ↔ νX = κ M • ν := by
  intro F E _ _ _ _ _ σ hσ d b s
  choose κ hκ0 hκ using GlobalTheory.T.exists_selfDualMeasure_global_const_rank_only F E σ hσ d b s
  refine ⟨κ, hκ0, ?_⟩
  intro M J β ψ ν hM hJ hβ hψ hν
  obtain ⟨mi, mv, hmi, hmv, hprod⟩ := hν
  obtain ⟨nI, nV⟩ := GlobalTheory.GaugeEx.nice_ainf_fv F
  have hβi : IsUnit (algebraMap F (Ainf F) β) := (isUnit_iff_ne_zero.2 hβ).map _
  have hβv : ∀ v : HeightOneSpectrum (𝓞 F), IsUnit (algebraMap F (Fv F v) β) :=
    fun v => (isUnit_iff_ne_zero.2 hβ).map _

  have key : ∀ μi, SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μi →
      ∀ νi, SdR (Ainf F) (psiInf F ψ) νi →
      ∀ μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) →
      ∀ νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v),
      (∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) →
      ∀ fibInf : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi
        {c : Ainf F | ∀ w, c w ≠ 0} fibInf →
      ∀ fibV : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v)
        {c | c ≠ 0} (fibV v)) →
      IsProd b (κ M • ν) (fibInf (algebraMap F (Ainf F) β))
        (fun v => fibV v (algebraMap F (Fv F v) β)) := by
    intro μi hμi νi hνi μv hμv νv hνv fibInf hfi fibV hfv
    obtain ⟨ri, ti, r, t, e1, e2, e3, e4, -, hti, -, ht, hfin, hk⟩ :=
      hκ M ψ J hψ hJ μi νi μv νv hμi hνi hμv hνv
    have a1 : fibInf (algebraMap F (Ainf F) β) = (ri / ti) • mi := by
      refine fib_eq_smul σ (Ainf F) nI J _ _ _ mi ri ti hti (e2 ▸ hνi.1) hβi hmi fibInf ?_
      rw [← e1, ← e2, ← units_inf]
      exact hfi
    have a2 : (fun v => fibV v (algebraMap F (Fv F v) β)) = fun v => (r v / t v) • mv v := by
      funext v
      refine fib_eq_smul σ (Fv F v) (nV v) J _ _ _ (mv v) (r v) (t v) (ht v) (e4 v ▸ (hνv v).1)
        (hβv v) (hmv v) (fibV v) ?_
      rw [← e3, ← e4, ← units_fv]
      exact hfv v
    rw [a1, a2, ← hk]
    exact GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul F E d b 1 M ν mi mv (ri / ti) (fun v => r v / t v) hprod hfin

  obtain ⟨⟨νi0, hνi0, -⟩, hWi⟩ := GlobalTheory.T.existsUnique_selfDual_haar_measure_infinite_adeles F E σ hσ ψ hψ
  obtain ⟨μi0, hμi0, -⟩ := hWi M J hJ
  choose νv0 hνv0 using fun v => (GlobalTheory.T.existsUnique_selfDual_measures_finitePlace F E σ hσ ψ hψ v).1.exists
  choose μv0 hμv0 using fun v => ((GlobalTheory.T.existsUnique_selfDual_measures_finitePlace F E σ hσ ψ hψ v).2 M J hJ).exists
  have exI : ∀ μi, SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μi →
      ∀ νi, SdR (Ainf F) (psiInf F ψ) νi →
      ∃ fibInf : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi
        {c : Ainf F | ∀ w, c w ≠ 0} fibInf :=
    fun μi hμi νi hνi => GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles F E σ hσ M J μi νi hM hJ hμi.1 hνi.1
  have exV : ∀ μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) →
      ∀ νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v),
      (∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) →
      ∃ fibV : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v)
        {c | c ≠ 0} (fibV v)) := by
    intro μv hμv νv hνv
    choose fibV hfibV using fun v =>
      (GlobalTheory.LocalDensityCompare.null_and_exists v σ J hσ hM hJ (μv v) (hμv v).1 (νv v) (hνv v).1).2
    exact ⟨fibV, hfibV⟩
  intro νX
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨fi, hfi⟩ := exI μi0 hμi0 νi0 hνi0
    obtain ⟨fv, hfv⟩ := exV μv0 hμv0 νv0 hνv0
    have h1 := (((((h.2 μi0 hμi0).2 νi0 hνi0).2 μv0 hμv0).2 νv0 hνv0).2 fi hfi).2 fv hfv
    have h2 := GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod F E d b 1 M _ _ _ (key μi0 hμi0 νi0 hνi0 μv0 hμv0 νv0 hνv0 fi hfi fv hfv)
    refine GlobalTheory.T.adelicTupleMeasure_ext_of_pureTensor_integrals F E d b 1 M _ _ fun Φ Φinf Φf Φv c1 c2 c3 c4 => ?_
    obtain ⟨p1, -, p3⟩ := h1 d b Φ Φinf Φf Φv c1 c2 c3 c4
    obtain ⟨q1, -, q3⟩ := h2 d b Φ Φinf Φf Φv c1 c2 c3 c4
    exact ⟨p1, q1, p3.trans q3.symm⟩
  · rintro rfl
    refine ⟨?_, ⟨μi0, hμi0⟩, fun μi hμi => ⟨⟨νi0, hνi0⟩, fun νi hνi => ⟨⟨μv0, hμv0⟩, fun μv hμv =>
      ⟨⟨νv0, hνv0⟩, fun νv hνv => ⟨exI μi hμi νi hνi, fun fi hfi => ⟨exV μv hμv νv hνv, fun fv hfv =>
      GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod F E d b 1 M _ _ _ (key μi hμi νi hνi μv hμv νv hνv fi hfi fv hfv)⟩⟩⟩⟩⟩⟩
    have hz := (GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 M ν mi mv hprod).2.2.2
      {Y | qR (Ainf F) σ J (Y 0) = algebraMap F _ β}
      (fun v => {Y | qR (Fv F v) σ J (Y 0) = algebraMap F _ β})
      (isClosed_eq (continuous_qR _ σ J) continuous_const).measurableSet
      (fun v => (isClosed_eq (continuous_qR _ σ J) continuous_const).measurableSet)
      (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ _ nI M J _ _ _ mi s.haar_nuI hβi hmi).1
      (fun v => (GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props F E σ _ (nV v) M J _ _ _ (mv v) (s.haar_nuV v) (hβv v) (hmv v)).1)
    have hs : {X : Fin 1 → Fin M → AF F ⊗[F] E | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} =
        {X | ¬ (projInf X ∈ {Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
            qR (Ainf F) σ J (Y 0) = algebraMap F _ β} ∧
          ∀ v, projV v (projFin X) ∈ {Y : Fin 1 → Fin M → Fv F v ⊗[F] E |
            qR (Fv F v) σ J (Y 0) = algebraMap F _ β})} := by
      ext X
      exact not_congr ((GlobalTheory.GaugeEx.q_and_unitary_local_components F E σ M J).1 (X 0) β)
    rw [Measure.smul_apply, hs, hz, smul_zero]

end GlobalTheory.GaugeEx
