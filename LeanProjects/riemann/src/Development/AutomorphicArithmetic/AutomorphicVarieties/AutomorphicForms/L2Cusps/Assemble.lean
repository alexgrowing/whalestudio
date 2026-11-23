import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_split (h : SplitEq) (s : {r : ℝ // 0 < r}) :
    ∃ t : ℝ, Reduction.centralSection E a s = splitCentre E a t := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, Subsingleton.elim _ _⟩
  · have h0 : ((a : ℝ) * Module.finrank ℚ E) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 ha.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
    refine ⟨Real.log s.1 / (a * Module.finrank ℚ E), ?_⟩
    rw [h]
    congr 1
    refine Subtype.ext ?_
    change s.1 = Real.exp _
    rw [mul_div_cancel₀ _ h0, Real.exp_log s.2]

omit [IsTotallyComplex E] in
theorem retractOne_surjective : Function.Surjective (retractOne : GA E a → G1 E a) :=
  fun x => ⟨x, retractOne_coe x⟩

theorem range_cmp (h1 : RangeLe) (h2 : ContMem) {μ : Measure (GA E a)} [μ.IsHaarMeasure]
    {μ₁ : Measure (G1 E a)} [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) :
    LinearMap.range (cmp hp).toLinearMap = L2cusp μ := by
  refine le_antisymm ?_ (L2cusp_le ?_ fun φ hφ h => h2 E a μ μ₁ hp φ hφ h)
  · rintro _ ⟨v, rfl⟩
    exact h1 E a μ μ₁ hp v
  · exact (cmp hp).isometry.isClosedEmbedding.isClosed_range

theorem partA (hH : MuHaar) (hP : QuotPres) (hE : CmpEquiv) (h1 : RangeLe) (h2 : ContMem) (hC : AbsCompact) :
    GlobalTheory.Published.CuspDiscreteDecompositionGL := by
  intro E _ _ _ a μ _ _
  have := hH E a μ
  have hp := hP E a μ
  exact EnoughCompact.isDiscreteSum (isUnitaryRep_Rcusp μ)
    (hC _ _ _ _ (cuspRepT (muOne μ)) (muOne μ) _ _ (isSubrep_L2cusp μ) (cmp hp) retractOne retractOne_surjective
      (hE E a μ _ hp) (range_cmp h1 h2 hp) fun f => isCompactOperator_cuspRep (muOne μ) f)

theorem partC (hS : SplitEq) (hB : BrCusp) : GlobalTheory.Published.CuspFormsBoundedGL := by
  intro E _ _ _ a φ hφ hn
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cuspForms (hB E a φ hφ)
  refine ⟨C, fun g => ?_⟩
  obtain ⟨s, y, hy, rfl⟩ := exists_centralSection_mul_mem_normOneGL g
  obtain ⟨t, ht⟩ := exists_split (E := E) (a := a) hS s
  rw [ht, hn]
  exact hC y hy

theorem partB (hS : SplitEq) (hH : MuHaar) (hP : QuotPres) (hE : CmpEquiv) (hF : CmpForm) (h1 : RangeLe) (h2 : ContMem)
    (hI : AbsIrr) (hN : NeBot) (hK : KFinTr) (hM : KFinMem) (hR : BrRep) : GlobalTheory.Published.CuspFiniteVectorsGL := by
  intro E _ _ _ a μ _ _ H hH' hirr
  have := hH E a μ
  have hp := hP E a μ
  have hle : H ≤ LinearMap.range (cmp hp).toLinearMap := (range_cmp h1 h2 hp).symm ▸ hH'
  obtain ⟨_, hV, hVi⟩ := hI _ _ _ _ (cuspRepT (muOne μ)) _ (cmp hp) retractOne retractOne_surjective
    (hE E a μ _ hp) H hle hirr
  have hne := hN E a _ _ hV hVi
  have hcl := CuspidalAutomorphicRepresentation.topologicalClosure_map_ofSummand _ hV hVi hne
  generalize CuspidalAutomorphicRepresentation.ofSummand _ hV hVi hne = π₀ at hcl
  obtain ⟨π, hπ⟩ := hR E a π₀
  have hto : ∀ φ ∈ π.V, ∃ ψ ∈ π₀.carrier, ψ.1 = φ.1 := fun φ hφ => hπ.le ⟨φ, hφ, rfl⟩
  have hof : ∀ ψ ∈ π₀.carrier, ∃ φ ∈ π.V, φ.1 = ψ.1 := fun ψ hψ => hπ.ge ⟨ψ, hψ, rfl⟩
  have hnorm : IsNormalised π := fun φ hφ t g => by
    obtain ⟨ψ, hψ, e⟩ := hto φ hφ
    rw [← e, hS]
    exact π₀.le_central hψ _ g
  have hcls : classes π.V μ = (π₀.carrier.map (cuspVecL (muOne μ))).map (cmp hp).toLinearMap := by
    ext F
    constructor
    · rintro ⟨φ, hφ, e⟩
      obtain ⟨ψ, hψ, e'⟩ := hto φ hφ
      exact ⟨_, ⟨ψ, hψ, rfl⟩, l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ((hF E a μ _ hp ψ (π₀.le_central hψ)).trans (e' ▸ e.symm))⟩
    · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      obtain ⟨φ, hφ, e⟩ := hof ψ hψ
      exact ⟨φ, hφ, e ▸ hF E a μ _ hp ψ (π₀.le_central hψ)⟩
  refine ⟨π, hnorm, fun φ hφ => ?_, ?_, fun F hFH hk => ?_⟩
  · obtain ⟨ψ, hψ, e⟩ := hto φ hφ
    exact memL2_of_ae_eq (leftInv_latticeGL (π.cusp φ hφ).1.left (hnorm φ hφ))
      (e ▸ hF E a μ _ hp ψ (π₀.le_central hψ))
  · rw [hcls, ← Submodule.map_comap_eq_self hle, ← hcl]
    refine SetLike.coe_injective ?_
    simp only [Submodule.topologicalClosure_coe, Submodule.map_coe]
    exact (cmp hp).isometry.isClosedEmbedding.closure_image_eq _
  · obtain ⟨v, rfl⟩ := hle hFH
    obtain ⟨k1, k2⟩ := hK E a μ _ hp v hk
    rw [hcls]
    exact ⟨v, hM E a _ π₀ v (hcl.symm ▸ hFH) k1 k2, rfl⟩

end UpperTheory.V.KernelIndexFullLattice
