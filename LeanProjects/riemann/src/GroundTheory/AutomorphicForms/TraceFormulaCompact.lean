import Mathlib
import GroundTheory.AutomorphicForms.DiscreteDecomposition
import GroundTheory.AutomorphicForms.TraceFormulaSpectral
import GroundTheory.AutomorphicForms.TraceFormulaMultiplicity
import GroundTheory.AutomorphicForms.TraceFormulaGeometric
import GroundTheory.AutomorphicForms.TraceFormulaCentralizer
import GroundTheory.AutomorphicForms.TraceFormulaWeil
import GroundTheory.AutomorphicForms.TraceFormulaConvolution

open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem hasSum_orbitalIntegral_of_rep (f : CompactlySupportedContinuousMap G ℂ)
    (hf : IsTraceClass ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)))
    (r : ConjClasses Γ → Γ) (hr : ∀ c, ConjClasses.mk (r c) = c) :
    HasSum (fun c : ConjClasses Γ =>
        ∫ x, conjOrbitFun (centralizerIn Γ ((r c : Γ) : G)) (centralizerIn_le_centralizer Γ _) f x
          ∂quotientMeasure (centralizerIn Γ ((r c : Γ) : G)) μ)
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) := by
  have h := hasSum_integral_conj Γ μ f hf
  rw [← (Equiv.sigmaFiberEquiv (ConjClasses.mk : Γ → ConjClasses Γ)).hasSum_iff] at h
  refine h.sigma fun c => ?_
  let e : {γ' : Γ // IsConj (r c) γ'} ≃ {γ' : Γ // ConjClasses.mk γ' = c} :=
    Equiv.subtypeEquivRight fun γ' => by
      have hc := hr c
      constructor
      · intro h'
        rw [← hc]
        exact ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_comm.1 h')
      · intro h'
        rw [← hc] at h'
        exact isConj_comm.1 (ConjClasses.mk_eq_mk_iff_isConj.1 h')
  have h2 := hasSum_integral_conj_isConj Γ μ f (r c)
  rw [← e.symm.hasSum_iff] at h2
  convert h2 using 1
  all_goals rfl

omit [μ.IsMulRightInvariant] in

theorem integrable_conjOrbitFun_centralizerIn (f : CompactlySupportedContinuousMap G ℂ) (γ : Γ) :
    Integrable (conjOrbitFun (centralizerIn Γ γ) (centralizerIn_le_centralizer Γ γ) f)
      (quotientMeasure (centralizerIn Γ γ) μ) := by
  classical
  have hδ : ∀ i : {γ' : Γ // IsConj γ γ'}, ∃ d : Γ, d⁻¹ * γ * d = i.1 := fun i => by
    obtain ⟨c, hc⟩ := isConj_iff.1 i.2
    exact ⟨c⁻¹, by rw [inv_inv]; exact hc⟩
  choose δ hδ using hδ
  have hD := (measure_fundamentalDomain_lt_top Γ μ).ne
  have hEμ : ∀ i : {γ' : Γ // IsConj γ γ'},
      μ (((δ i : Γ) : G) • fundamentalDomain Γ) ≠ ∞ := fun i => by
    rw [measure_smul]; exact hD
  have hconj : ∀ (i : {γ' : Γ // IsConj γ γ'}) (x : G),
      ((δ i : G) * x)⁻¹ * γ * ((δ i : G) * x) = x⁻¹ * (i.1 : G) * x := by
    intro i x
    have := congrArg Subtype.val (hδ i)
    push_cast at this
    rw [← this]
    group
  have hnorm : ∀ i : {γ' : Γ // IsConj γ γ'},
      ∫ x in ((δ i : Γ) : G) • fundamentalDomain Γ, ‖f (x⁻¹ * (γ : G) * x)‖ ∂μ =
        ∫ x in fundamentalDomain Γ, ‖f (x⁻¹ * (i.1 : G) * x)‖ ∂μ := by
    intro i
    rw [setIntegral_smul_set μ]
    simp_rw [hconj]
  have hint : IntegrableOn (fun x => f (x⁻¹ * (γ : G) * x))
      (⋃ i, ((δ i : Γ) : G) • fundamentalDomain Γ) μ := by
    refine integrableOn_iUnion_of_summable_integral_norm
      (fun i => integrableOn_conj μ f _ (hEμ i)) ?_
    simp_rw [hnorm]
    exact (summable_integral_norm_conj Γ μ f).comp_injective Subtype.val_injective
  have hmeas : Measurable (conjOrbitFun (centralizerIn Γ γ) (centralizerIn_le_centralizer Γ γ) f) :=
    measurable_from_quotient.2 (f.continuous.comp (by fun_prop)).measurable
  rw [← map_restrict_eq_quotientMeasure μ (isFundamentalDomain_iUnion_smul Γ μ γ hδ),
    integrable_map_measure hmeas.aestronglyMeasurable (measurable_mk _).aemeasurable]
  exact hint

omit [μ.IsMulRightInvariant] in

theorem integrable_conjOrbitFun_of_isWeilMeasure (f : CompactlySupportedContinuousMap G ℂ)
    (γ : Γ) (ν : Measure (Subgroup.centralizer {(γ : G)})) [ν.IsHaarMeasure]
    {ρ : Measure (RightCosetSpace (Subgroup.centralizer {(γ : G)}))}
    (hρ : IsWeilMeasure (Subgroup.centralizer {(γ : G)}) μ ν ρ) :
    Integrable (conjOrbitFun (Subgroup.centralizer {(γ : G)}) le_rfl f) ρ := by
  obtain ⟨h0, htop⟩ := quotientMeasure_centralizerLattice_univ_ne_zero_ne_top Γ γ ν
  have hmeas : Measurable (conjOrbitFun (Subgroup.centralizer {(γ : G)}) le_rfl f) :=
    measurable_from_quotient.2 (f.continuous.comp (by fun_prop)).measurable
  have hcomp : conjOrbitFun (Subgroup.centralizer {(γ : G)}) le_rfl f ∘
      mapOfLe (centralizerIn_le_centralizer Γ γ) =
        conjOrbitFun (centralizerIn Γ γ) (centralizerIn_le_centralizer Γ γ) f := by
    funext y
    obtain ⟨x, rfl⟩ := mk_surjective _ y
    rfl
  have h1 : Integrable (conjOrbitFun (Subgroup.centralizer {(γ : G)}) le_rfl f)
      (quotientMeasure (centralizerLattice Γ (γ : G)) ν univ • ρ) := by
    rw [smul_eq_map_of_isWeilMeasure Γ μ (γ : G) ν hρ,
      integrable_map_measure hmeas.aestronglyMeasurable (measurable_mapOfLe _).aemeasurable, hcomp]
    exact integrable_conjOrbitFun_centralizerIn Γ μ f γ
  have h2 := h1.smul_measure (ENNReal.inv_ne_top.2 h0)
  rwa [smul_smul, ENNReal.inv_mul_cancel h0 htop, one_smul] at h2

theorem traceFormula (f : CompactlySupportedContinuousMap G ℂ)
    (hf : IsTraceClass ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)))
    {s : Set (Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))}
    [∀ V : s, CompleteSpace (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))]
    (hinv : ∀ V : s, (rightRegularRep Γ μ).IsInvariant V)
    (hsum : IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))))
      fun V => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))).subtypeₗᵢ)
    (hirr : ∀ V : s, ((rightRegularRep Γ μ).restrict V (hinv V)).IsIrreducible)
    (r : ConjClasses Γ → Γ) (hr : ∀ c, ConjClasses.mk (r c) = c)
    (ν : ∀ c : ConjClasses Γ, Measure (Subgroup.centralizer {((r c : Γ) : G)}))
    (hν : ∀ c, (ν c).IsHaarMeasure)
    (ρ : ∀ c : ConjClasses Γ, Measure (RightCosetSpace (Subgroup.centralizer {((r c : Γ) : G)})))
    (hρ : ∀ c, IsWeilMeasure (Subgroup.centralizer {((r c : Γ) : G)}) μ (ν c) (ρ c)) :
    HasSum (fun π : Quotient (UnitaryRep.restrictSetoid (rightRegularRep Γ μ) hinv) =>
        (UnitaryRep.multiplicity (rightRegularRep Γ μ) hinv π : ℂ) *
          trace (((rightRegularRep Γ μ).restrict π.out (hinv π.out)).integrated μ
            (UnitaryRep.ccToL1 μ f)))
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) ∧
    HasSum (fun c : ConjClasses Γ =>
        (quotientMeasure (centralizerLattice Γ ((r c : Γ) : G)) (ν c) univ).toReal •
          ∫ y, conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl f y ∂ρ c)
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) ∧
    ∀ c, Integrable (conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl f) (ρ c) := by
  refine ⟨UnitaryRep.hasSum_multiplicity_mul_trace hinv hsum hf (fun V => UnitaryRep.finite_setOf_isEquivalent (isCompactOperator_integrated Γ μ) hinv
      hsum.OrthogonalFamily (hirr V)), ?_, fun c => ?_⟩
  · convert hasSum_orbitalIntegral_of_rep Γ μ f hf r hr using 1
    funext c
    have := hν c
    exact (integral_conjOrbitFun_eq_smul Γ μ _ (ν c) (hρ c) f).symm
  · have := hν c
    exact integrable_conjOrbitFun_of_isWeilMeasure Γ μ f (r c) (ν c) (hρ c)

theorem multiplicity_eq_finrank_intertwiners
    {s : Set (Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))}
    [∀ V : s, CompleteSpace (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))]
    (hinv : ∀ V : s, (rightRegularRep Γ μ).IsInvariant V)
    (hsum : IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))))
      fun V => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))).subtypeₗᵢ)
    (hirr : ∀ V : s, ((rightRegularRep Γ μ).restrict V (hinv V)).IsIrreducible)
    (π : Quotient (UnitaryRep.restrictSetoid (rightRegularRep Γ μ) hinv)) :
    UnitaryRep.multiplicity (rightRegularRep Γ μ) hinv π =
      Module.finrank ℂ (((rightRegularRep Γ μ).restrict π.out (hinv π.out)).intertwiners
        (rightRegularRep Γ μ)) :=
  (UnitaryRep.multiplicity_eq_finrank hinv hsum hirr (fun V => UnitaryRep.finite_setOf_isEquivalent (isCompactOperator_integrated Γ μ) hinv
      hsum.OrthogonalFamily (hirr V)) π (UnitaryRep.IsEquivalent.refl _)).2

theorem tsum_spectral_eq_tsum_geometric (f : CompactlySupportedContinuousMap G ℂ)
    (hf : IsTraceClass ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)))
    {s : Set (Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))}
    [∀ V : s, CompleteSpace (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))]
    (hinv : ∀ V : s, (rightRegularRep Γ μ).IsInvariant V)
    (hsum : IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))))
      fun V => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))).subtypeₗᵢ)
    (hirr : ∀ V : s, ((rightRegularRep Γ μ).restrict V (hinv V)).IsIrreducible)
    (r : ConjClasses Γ → Γ) (hr : ∀ c, ConjClasses.mk (r c) = c)
    (ν : ∀ c : ConjClasses Γ, Measure (Subgroup.centralizer {((r c : Γ) : G)}))
    (hν : ∀ c, (ν c).IsHaarMeasure)
    (ρ : ∀ c : ConjClasses Γ, Measure (RightCosetSpace (Subgroup.centralizer {((r c : Γ) : G)})))
    (hρ : ∀ c, IsWeilMeasure (Subgroup.centralizer {((r c : Γ) : G)}) μ (ν c) (ρ c)) :
    ∑' π : Quotient (UnitaryRep.restrictSetoid (rightRegularRep Γ μ) hinv),
        (UnitaryRep.multiplicity (rightRegularRep Γ μ) hinv π : ℂ) *
          trace (((rightRegularRep Γ μ).restrict π.out (hinv π.out)).integrated μ
            (UnitaryRep.ccToL1 μ f)) =
      ∑' c : ConjClasses Γ,
        (quotientMeasure (centralizerLattice Γ ((r c : Γ) : G)) (ν c) univ).toReal •
          ∫ y, conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl f y ∂ρ c := by
  obtain ⟨h1, h2, -⟩ := traceFormula Γ μ f hf hinv hsum hirr r hr ν hν ρ hρ
  rw [h1.tsum_eq, h2.tsum_eq]

theorem traceFormula_conv (f₁ f₂ : CompactlySupportedContinuousMap G ℂ)
    {s : Set (Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))}
    [∀ V : s, CompleteSpace (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))]
    (hinv : ∀ V : s, (rightRegularRep Γ μ).IsInvariant V)
    (hsum : IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))))
      fun V => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))).subtypeₗᵢ)
    (hirr : ∀ V : s, ((rightRegularRep Γ μ).restrict V (hinv V)).IsIrreducible)
    (r : ConjClasses Γ → Γ) (hr : ∀ c, ConjClasses.mk (r c) = c)
    (ν : ∀ c : ConjClasses Γ, Measure (Subgroup.centralizer {((r c : Γ) : G)}))
    (hν : ∀ c, (ν c).IsHaarMeasure)
    (ρ : ∀ c : ConjClasses Γ, Measure (RightCosetSpace (Subgroup.centralizer {((r c : Γ) : G)})))
    (hρ : ∀ c, IsWeilMeasure (Subgroup.centralizer {((r c : Γ) : G)}) μ (ν c) (ρ c)) :
    HasSum (fun π : Quotient (UnitaryRep.restrictSetoid (rightRegularRep Γ μ) hinv) =>
        (UnitaryRep.multiplicity (rightRegularRep Γ μ) hinv π : ℂ) *
          trace (((rightRegularRep Γ μ).restrict π.out (hinv π.out)).integrated μ
            (UnitaryRep.ccToL1 μ (conv μ f₁ f₂))))
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ (conv μ f₁ f₂)))) ∧
    HasSum (fun c : ConjClasses Γ =>
        (quotientMeasure (centralizerLattice Γ ((r c : Γ) : G)) (ν c) univ).toReal •
          ∫ y, conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl (conv μ f₁ f₂) y ∂ρ c)
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ (conv μ f₁ f₂)))) ∧
    ∀ c, Integrable (conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl (conv μ f₁ f₂)) (ρ c) :=
  traceFormula Γ μ (conv μ f₁ f₂) (isTraceClass_integrated_conv Γ μ f₁ f₂) hinv hsum hirr r hr ν
    hν ρ hρ

theorem traceFormula_of_isLocallyConstant [TotallyDisconnectedSpace G]
    (f : CompactlySupportedContinuousMap G ℂ) (hf : IsLocallyConstant (f : G → ℂ))
    {s : Set (Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))}
    [∀ V : s, CompleteSpace (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))]
    (hinv : ∀ V : s, (rightRegularRep Γ μ).IsInvariant V)
    (hsum : IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))))
      fun V => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))).subtypeₗᵢ)
    (hirr : ∀ V : s, ((rightRegularRep Γ μ).restrict V (hinv V)).IsIrreducible)
    (r : ConjClasses Γ → Γ) (hr : ∀ c, ConjClasses.mk (r c) = c)
    (ν : ∀ c : ConjClasses Γ, Measure (Subgroup.centralizer {((r c : Γ) : G)}))
    (hν : ∀ c, (ν c).IsHaarMeasure)
    (ρ : ∀ c : ConjClasses Γ, Measure (RightCosetSpace (Subgroup.centralizer {((r c : Γ) : G)})))
    (hρ : ∀ c, IsWeilMeasure (Subgroup.centralizer {((r c : Γ) : G)}) μ (ν c) (ρ c)) :
    HasSum (fun π : Quotient (UnitaryRep.restrictSetoid (rightRegularRep Γ μ) hinv) =>
        (UnitaryRep.multiplicity (rightRegularRep Γ μ) hinv π : ℂ) *
          trace (((rightRegularRep Γ μ).restrict π.out (hinv π.out)).integrated μ
            (UnitaryRep.ccToL1 μ f)))
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) ∧
    HasSum (fun c : ConjClasses Γ =>
        (quotientMeasure (centralizerLattice Γ ((r c : Γ) : G)) (ν c) univ).toReal •
          ∫ y, conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl f y ∂ρ c)
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) ∧
    ∀ c, Integrable (conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl f) (ρ c) :=
  traceFormula Γ μ f (isTraceClass_integrated_of_isLocallyConstant Γ μ f hf) hinv hsum hirr r hr
    ν hν ρ hρ

theorem traceFormula_haar (f : CompactlySupportedContinuousMap G ℂ)
    (hf : IsTraceClass ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f)))
    {s : Set (Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))}
    [∀ V : s, CompleteSpace (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ)))]
    (hinv : ∀ V : s, (rightRegularRep Γ μ).IsInvariant V)
    (hsum : IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))))
      fun V => (V : Submodule ℂ (Lp ℂ 2 (quotientMeasure Γ μ))).subtypeₗᵢ)
    (hirr : ∀ V : s, ((rightRegularRep Γ μ).restrict V (hinv V)).IsIrreducible)
    (r : ConjClasses Γ → Γ) (hr : ∀ c, ConjClasses.mk (r c) = c)
    (ν : ∀ c : ConjClasses Γ, Measure (Subgroup.centralizer {((r c : Γ) : G)}))
    (hν : ∀ c, (ν c).IsHaarMeasure) :
    HasSum (fun π : Quotient (UnitaryRep.restrictSetoid (rightRegularRep Γ μ) hinv) =>
        (UnitaryRep.multiplicity (rightRegularRep Γ μ) hinv π : ℂ) *
          trace (((rightRegularRep Γ μ).restrict π.out (hinv π.out)).integrated μ
            (UnitaryRep.ccToL1 μ f)))
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) ∧
    HasSum (fun c : ConjClasses Γ =>
        (quotientMeasure (centralizerLattice Γ ((r c : Γ) : G)) (ν c) univ).toReal •
          ∫ y, conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl f y ∂weilMeasure Γ μ (r c) (ν c))
      (trace ((rightRegularRep Γ μ).integrated μ (UnitaryRep.ccToL1 μ f))) ∧
    ∀ c, Integrable (conjOrbitFun (Subgroup.centralizer {((r c : Γ) : G)}) le_rfl f) (weilMeasure Γ μ (r c) (ν c)) :=
  traceFormula Γ μ f hf hinv hsum hirr r hr ν hν (fun c => weilMeasure Γ μ (r c) (ν c))
    (fun c => by have := hν c; exact isWeilMeasure_weilMeasure Γ μ (r c) (ν c))

end RightCosetSpace

end

end GroundTheory.Automorphic
