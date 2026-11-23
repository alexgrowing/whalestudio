import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometry
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalKerSubId
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDense
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC PositivityTheory.Affgl

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspInvariant

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem memL2_of_bounded_continuous_invariant (μ : Measure (GA E a)) [μ.IsHaarMeasure] {φ : GA E a → ℂ} (hc : Continuous φ)
    (hl : LeftInv (latticeGL E a) φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) : MemL2Quotient (latticeGL E a) μ φ := by
  have hfin := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  refine ⟨hl, MemLp.of_bound ?_ C (.of_forall fun q => hC _)⟩
  refine aestronglyMeasurable_quotMeasure_iff_lift.2 ?_
  rw [hl.lift_descend]
  exact hc.aestronglyMeasurable

theorem repOp_toL2cusp (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f φ : GA E a → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (h : MemL2Quotient (latticeGL E a) μ φ) (hm : φ ∈ cuspCont E a)
    (hφ : ∀ x, convR μ f φ x = φ x) :
    repOp (Rcusp μ) μ f ⟨h.toL2, toL2_mem_cuspidal h hm⟩ = ⟨h.toL2, toL2_mem_cuspidal h hm⟩ := by
  have hi : Integrable f μ := hf.integrable_of_hasCompactSupport hs
  have hT : IsRepOp (R (latticeGL E a) μ) μ f (Rop (latticeGL E a) μ f) := isRepOp_Rop hi
  refine Subtype.ext (((isSubrep_L2cusp μ).coe_repOp_rep hT).2 _ |>.trans ?_)
  refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
  have e := h.lift_toL2_ae_eq
  refine (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ _ μ f hi h.toL2).2.trans
    (Filter.EventuallyEq.trans (.of_forall fun x => ?_) e.symm)
  rw [← hφ x]
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_mul_left μ x).quasiMeasurePreserving.ae e] with y hy
  rw [hy]

theorem finiteDimensional_span (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA E a → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (S : Set (GA E a → ℂ))
    (hS : ∀ φ ∈ S, φ ∈ cuspCont E a ∧ (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ ∀ x, convR μ f φ x = φ x) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  have hA := GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp E a μ f hf hs
  have hK := GlobalTheory.CompanionTheory.CompactFix.finiteDimensional_ker_sub_id _ hA
  set K := LinearMap.ker (((repOp (Rcusp μ) μ f : L2cusp μ →L[ℂ] L2cusp μ) : L2cusp μ →ₗ[ℂ] L2cusp μ) - LinearMap.id)
  let t := GlobalTheory.CompanionTheory.CuspTransfer.toL2cusp μ
  have ht : Function.Injective t := (injective_iff_map_eq_zero _).2 fun φ e => Subtype.ext (by
    by_contra h0
    exact toL2_ne_zero φ.2.2 φ.2.1.1 h0 (congrArg Subtype.val e))
  let Q := K.comap t
  have hQ : FiniteDimensional ℂ Q := FiniteDimensional.of_injective (t.restrict (q := K) fun x hx => hx)
    fun x y e => Subtype.ext (ht (congrArg Subtype.val e))
  have hle : Submodule.span ℂ S ≤ Q.map (GlobalTheory.CompanionTheory.CuspTransfer.cuspidalL2Functions μ).subtype := Submodule.span_le.2 fun φ hφ => by
    obtain ⟨h1, ⟨C, hC⟩, h3⟩ := hS φ hφ
    have hm := memL2_of_bounded_continuous_invariant μ h1.1 (leftInv_of_mem_cuspCont h1) hC
    refine ⟨⟨φ, h1, hm⟩, ?_, rfl⟩
    change _ ∈ K
    simp only [K, LinearMap.mem_ker, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
    exact sub_eq_zero.2 (repOp_toL2cusp μ hf hs hm h1 h3)
  exact Submodule.finiteDimensional_of_le hle

theorem exists_compact_open {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) :
    ∃ U : Subgroup (GL (Fin a) (Af E)), U ≤ L ∧ IsOpen (U : Set (GL (Fin a) (Af E))) ∧
      IsCompact (U : Set (GL (Fin a) (Af E))) := by
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : GA E a)
  have hc := ContAut.continuous_map_pFin E a
  have hW : (GeneralLinearGroup.map (pFin E) '' C : Set (GL (Fin a) (Af E))) ∈ 𝓝 (1 : GL (Fin a) (Af E)) := by
    have h1 : finGL E a ⁻¹' C ∈ 𝓝 (1 : GL (Fin a) (Af E)) :=
      (GlobalTheory.CompanionTheory.DenseKFin.continuous_finGL (E := E) (a := a)).continuousAt.preimage_mem_nhds (by simpa using hC1)
    exact Filter.mem_of_superset h1 fun k hk => ⟨_, hk, pFin_finGL k⟩
  obtain ⟨U, hU, hUW⟩ := GlobalTheory.CompanionTheory.DenseKFin.exists_openSubgroup_GLAf (Filter.inter_mem hW (hL.mem_nhds (one_mem L)))
  exact ⟨U, fun k hk => (hUW hk).2, hU, (hC.image hc).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hU)
    fun k hk => (hUW hk).1⟩

abbrev pI (g : GA E a) : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g

def levelSet (U : Subgroup (GL (Fin a) (Af E))) : Set (GA E a) := {g | GeneralLinearGroup.map (pFin E) g ∈ U}

theorem isClopen_levelSet {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) :
    IsClopen (levelSet U : Set (GA E a)) :=
  ⟨(Subgroup.isClosed_of_isOpen U hU).preimage (ContAut.continuous_map_pFin E a),
    hU.preimage (ContAut.continuous_map_pFin E a)⟩

theorem isCompact_levelSet_inter {U : Subgroup (GL (Fin a) (Af E))} (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    {K : Set (GL (Fin a) (Cinf E))} (hK : IsCompact K) : IsCompact ((levelSet U : Set (GA E a)) ∩ pI ⁻¹' K) := by
  have e : (levelSet U : Set (GA E a)) ∩ pI ⁻¹' K =
      (GASplit.splitEquiv E a).toHomeomorph ⁻¹' (K ×ˢ (U : Set (GL (Fin a) (Af E)))) := by
    ext g
    exact and_comm
  rw [e]
  exact (Homeomorph.isCompact_preimage _).2 (hK.prod hU)

section Measure

variable [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]

def levelMeasure (μ : Measure (GA E a)) (U : Subgroup (GL (Fin a) (Af E))) : Measure (GL (Fin a) (Cinf E)) :=
  (μ.restrict (levelSet U)).map pI

theorem measurable_pI : Measurable (pI : GA E a → GL (Fin a) (Cinf E)) :=
  (ContAut.continuous_map_pInf E a).measurable

theorem isHaarMeasure_levelMeasure (μ : Measure (GA E a)) [μ.IsHaarMeasure] {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) :
    (levelMeasure μ U).IsHaarMeasure := by
  haveI : T2Space (GL (Fin a) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
  have hH := (isClopen_levelSet hU).isOpen.measurableSet
  have hp := measurable_pI (E := E) (a := a)
  have hmeas : ∀ {K : Set (GL (Fin a) (Cinf E))}, MeasurableSet K →
      levelMeasure μ U K = μ (pI ⁻¹' K ∩ levelSet U) := fun hK => by
    rw [levelMeasure, Measure.map_apply hp hK, Measure.restrict_apply (hp hK)]
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [hmeas hK.measurableSet, Set.inter_comm]
    exact (isCompact_levelSet_inter hUc hK).measure_lt_top
  · intro y
    have hpre : (fun g : GA E a => infGL E a y * g) ⁻¹' levelSet U = levelSet U := by
      ext g
      simp [levelSet]
    have hmp := (measurePreserving_mul_left μ (infGL E a y)).restrict_preimage hH
    rw [hpre] at hmp
    rw [levelMeasure, Measure.map_map (measurable_const_mul y) hp]
    have e : ((fun x => y * x) ∘ pI : GA E a → _) = pI ∘ fun g => infGL E a y * g := by
      funext g
      simp
    rw [e, ← Measure.map_map hp (measurable_const_mul _), hmp.map_eq]
  · intro V hV hne
    obtain ⟨y, hy⟩ := hne
    rw [hmeas hV.measurableSet]
    refine ((hV.preimage (ContAut.continuous_map_pInf E a)).inter (isClopen_levelSet hU).isOpen).measure_ne_zero μ
      ⟨infGL E a y, by simpa using hy, ?_⟩
    simp [levelSet, one_mem]

theorem integral_levelMeasure (μ : Measure (GA E a)) {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) {α : GL (Fin a) (Cinf E) → ℂ} (hα : Continuous α) {φ : GA E a → ℂ}
    (hφ : Continuous φ) (hfix : ∀ k ∈ U, ∀ x, φ (x * finGL E a k) = φ x) (g : GA E a) :
    ∫ y, φ (g * infGL E a y) * α y ∂levelMeasure μ U = convR μ ((levelSet U).indicator (α ∘ pI)) φ g := by
  have hH := (isClopen_levelSet (E := E) hU).isOpen.measurableSet
  have hc : Continuous fun y => φ (g * infGL E a y) * α y :=
    (hφ.comp (continuous_const.mul GlobalTheory.CompanionTheory.DenseKFin.continuous_infGL)).mul hα
  rw [levelMeasure, integral_map measurable_pI.aemeasurable hc.aestronglyMeasurable]
  have e : (fun y => (levelSet U).indicator (α ∘ pI) y * φ (g * y)) =
      (levelSet U).indicator fun y => α (pI y) * φ (g * y) := by
    funext y
    by_cases h : y ∈ levelSet U <;> simp [h]
  rw [convR, e, integral_indicator hH]
  refine setIntegral_congr_fun hH fun y hy => ?_
  have h := hfix _ hy (g * infGL E a (pI y))
  rw [mul_assoc, infGL_mul_finGL] at h
  simp only [h, mul_comm]

end Measure

theorem continuous_test {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E))))
    {α : GL (Fin a) (Cinf E) → ℂ} (hα : Continuous α) :
    Continuous ((levelSet U : Set (GA E a)).indicator (α ∘ pI)) :=
  (hα.comp (ContAut.continuous_map_pInf E a)).indicator fun x hx => by
    rw [(isClopen_levelSet hU).frontier_eq] at hx
    exact absurd hx (Set.notMem_empty x)

theorem hasCompactSupport_test {U : Subgroup (GL (Fin a) (Af E))} (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    {α : GL (Fin a) (Cinf E) → ℂ} (hα : HasCompactSupport α) :
    HasCompactSupport ((levelSet U : Set (GA E a)).indicator (α ∘ pI)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_levelSet_inter hU hα) fun g hg => ?_
  rw [Function.mem_support] at hg
  have h1 : g ∈ levelSet U := by
    by_contra h
    exact hg (Set.indicator_of_notMem h _)
  refine ⟨h1, subset_tsupport _ ?_⟩
  rw [Function.mem_support]
  rwa [Set.indicator_of_mem h1] at hg

theorem cuspInvFin (hb : GlobalTheory.Published.CuspFormsBoundedGL)
    (hu : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), UnifAlpha E a) :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), CuspInvFin E a := by
  intro E _ _ _ a L hL W _ _ _ ρ hρ J hJ
  obtain ⟨U, hUL, hUo, hUc⟩ := exists_compact_open hL
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  let μ : Measure (GA E a) := Measure.haar
  haveI := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨α, hαc, hαs, hα⟩ := hu E a W ρ hρ J hJ (levelMeasure μ U) (isHaarMeasure_levelMeasure μ hUo hUc)
  set S : Set (Sm E a) := {φ | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 ∧
    ∀ t g, φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = φ.1 g} with hSdef
  have key := finiteDimensional_span μ (continuous_test hUo hαc) (hasCompactSupport_test hUc hαs)
    ((Sm E a).subtype '' S) (by
      rintro _ ⟨φ, ⟨hφ, hcusp, hz⟩, rfl⟩
      have hcf : IsCuspForm φ := ⟨hφ.1, hcusp⟩
      have hm := mem_cuspCont_of_isCuspForm hcf hz
      refine ⟨hm, hb.of_invariant hcf hz, fun x => ?_⟩
      refine (integral_levelMeasure μ hUo hαc hm.1 (fun k hk y => ?_) x).symm.trans (hα L φ hφ x).symm
      exact congrFun (congrArg Subtype.val (hφ.2.1 k (hUL hk))) y)
  rw [← Submodule.map_span] at key
  exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm.finiteDimensional

end GlobalTheory.CompanionTheory.CuspInvariant

end
