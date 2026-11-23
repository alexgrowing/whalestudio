import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.UnitsBorelSpace.BorelSpaceDoubledGroup
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.BlockTriangularFrames.SiegelParabolicEqStabiliserCols
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance matrixSpaceT2 {p q : ℕ} : T2Space (Mx F E p q) := inferInstanceAs (T2Space (Fin p → Fin q → AE F E))

instance mxLC {p q : ℕ} : LocallyCompactSpace (Mx F E p q) :=
  inferInstanceAs (LocallyCompactSpace (Fin p → Fin q → AE F E))

instance mxSC {p q : ℕ} : SecondCountableTopology (Mx F E p q) :=
  inferInstanceAs (SecondCountableTopology (Fin p → Fin q → AE F E))

instance mxTAG {p q : ℕ} : IsTopologicalAddGroup (Mx F E p q) :=
  inferInstanceAs (IsTopologicalAddGroup (Fin p → Fin q → AE F E))

instance mxBorel {p q : ℕ} : BorelSpace (Mx F E p q) := inferInstanceAs (BorelSpace (Fin p → Fin q → AE F E))

variable (F E) in

abbrev bsE : Module.Basis (Fin (Module.finrank F E)) F E := Module.finBasis F E

variable (F E) in

abbrev bsA : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) (bsE F E)

theorem inclR_eq (x : E) : inclR (F := F) (AF F) x = (1 : AF F) ⊗ₜ[F] x := rfl

theorem continuous_coord (k : Fin (Module.finrank F E)) : Continuous fun z : AE F E => (bsA F E).repr z k := by
  exact IsModuleTopology.continuous_of_linearMap (R := AF F) ((bsA F E).coord k)

theorem coord_inclR (x : E) (k : Fin (Module.finrank F E)) :
    (bsA F E).repr (inclR (F := F) (AF F) x) k = algebraMap F (AF F) ((bsE F E).repr x k) := by
  rw [inclR_eq, Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem exists_nhds_inclR : ∃ V ∈ 𝓝 (0 : AE F E), ∀ x : E, inclR (F := F) (AF F) x ∈ V → x = 0 := by
  obtain ⟨U, hU, hU0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  refine ⟨⋂ k, (fun z : AE F E => (bsA F E).repr z k) ⁻¹' U, ?_, ?_⟩
  · refine Filter.iInter_mem.2 fun k => ?_
    exact (continuous_coord k).continuousAt.preimage_mem_nhds (by simpa using hU)
  · intro x hx
    have h : ∀ k, (bsE F E).repr x k = 0 := by
      intro k
      apply hU0
      rw [← coord_inclR]
      exact Set.mem_iInter.1 hx k
    exact (bsE F E).forall_coord_eq_zero_iff.1 h

theorem exists_compact_AE : ∃ C : Set (AE F E), IsCompact C ∧ ∀ z : AE F E, ∃ x : E, inclR (F := F) (AF F) x + z ∈ C := by
  obtain ⟨K, hK, hKa⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  refine ⟨(bsA F E).equivFun.symm '' Set.univ.pi (fun _ => K), ?_, ?_⟩
  · exact (isCompact_univ_pi fun _ => hK).image
      (IsModuleTopology.continuous_of_linearMap (bsA F E).equivFun.symm.toLinearMap)
  · intro z
    choose y hy using fun k => hKa ((bsA F E).repr z k)
    have hx : ∀ k, (bsE F E).repr ((bsE F E).equivFun.symm (-y)) k = -y k := by
      intro k
      rw [← (bsE F E).equivFun_apply, LinearEquiv.apply_symm_apply]
      rfl
    refine ⟨(bsE F E).equivFun.symm (-y),
      (bsA F E).equivFun (inclR (F := F) (AF F) ((bsE F E).equivFun.symm (-y)) + z), ?_, ?_⟩
    · intro k _
      rw [(bsA F E).equivFun_apply, map_add, Finsupp.add_apply, coord_inclR, hx, map_neg, neg_add_eq_sub]
      exact hy k
    · exact LinearEquiv.symm_apply_apply _ _

variable (F E) in

def ratMx (p q : ℕ) : AddSubgroup (Mx F E p q) :=
  AddSubgroup.closure (Set.range fun X : Matrix (Fin p) (Fin q) E => incM F X)

theorem ratM_eq {σ : E →ₐ[F] E} (d : SD σ) : d.ratM = ratMx F E d.m d.n := rfl

theorem incM_add {α β : Type} (X Z : Matrix α β E) : incM F (X + Z) = incM F X + incM F Z := by
  simp [incM, Matrix.map_add]

theorem incM_neg {α β : Type} (X : Matrix α β E) : incM F (-X) = -incM F X := by
  simp [incM, Matrix.map_neg]

theorem incM_zero {α β : Type} : incM F (0 : Matrix α β E) = 0 := by
  simp [incM]

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
  haveI : Nontrivial (AF F) := by
    show Nontrivial (AdeleRing (𝓞 F) F)
    unfold AdeleRing
    infer_instance
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective

theorem incM_injective {α β : Type} : Function.Injective (incM F : Matrix α β E → Matrix α β (AE F E)) := by
  intro X Z h
  ext i j
  exact inclR_injective (congrFun (congrFun h i) j)

theorem mem_ratMx {p q : ℕ} {x : Mx F E p q} : x ∈ ratMx F E p q ↔ ∃ X, incM F X = x := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, incM_zero⟩
    | add x y _ _ hx hy =>
      obtain ⟨X, rfl⟩ := hx
      obtain ⟨Z, rfl⟩ := hy
      exact ⟨X + Z, incM_add X Z⟩
    | neg x _ hx =>
      obtain ⟨X, rfl⟩ := hx
      exact ⟨-X, incM_neg X⟩
  · rintro ⟨X, rfl⟩
    exact AddSubgroup.subset_closure ⟨X, rfl⟩

theorem coe_ratMx (p q : ℕ) : (ratMx F E p q : Set (Mx F E p q)) = Set.range (incM F) := by
  ext x
  exact mem_ratMx

instance ratMx_discrete {p q : ℕ} : DiscreteTopology (ratMx F E p q) := by
  obtain ⟨V, hV, hV0⟩ := exists_nhds_inclR (F := F) (E := E)
  have hW : (⋂ i, ⋂ j, (fun M : Mx F E p q => M i j) ⁻¹' V) ∈ 𝓝 (0 : Mx F E p q) := by
    refine Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => ?_
    exact ((continuous_apply j).comp (continuous_apply i)).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨O, hOW, hO, h0⟩ := mem_nhds_iff.1 hW
  refine discreteTopology_of_isOpen_singleton_zero ?_
  convert hO.preimage (continuous_subtype_val (p := fun x => x ∈ ratMx F E p q)) using 1
  ext ⟨x, hx⟩
  constructor
  · intro h
    have h1 : x = 0 := congrArg Subtype.val (Set.mem_singleton_iff.1 h)
    subst h1
    exact h0
  · intro h
    obtain ⟨X, rfl⟩ := mem_ratMx.1 hx
    have h2 : X = 0 := by
      ext i j
      have := Set.mem_iInter.1 (Set.mem_iInter.1 (hOW h) i) j
      exact hV0 _ this
    subst h2
    exact Set.mem_singleton_iff.2 (Subtype.ext incM_zero)

theorem countable_E : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable

instance ratMx_countable {p q : ℕ} : Countable (ratMx F E p q) := by
  haveI := countable_E (E := E)
  haveI : Countable (Matrix (Fin p) (Fin q) E) := inferInstanceAs (Countable (Fin p → Fin q → E))
  have h : (ratMx F E p q : Set (Mx F E p q)).Countable := by
    rw [coe_ratMx]
    exact Set.countable_range _
  exact h.to_subtype

theorem ratMx_cocompact (p q : ℕ) : ∃ K : Set (Mx F E p q), IsCompact K ∧ ∀ x, ∃ γ ∈ ratMx F E p q, γ + x ∈ K := by
  obtain ⟨C, hC, hCx⟩ := exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi fun _ => Set.univ.pi fun _ => C,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC, fun x => ?_⟩
  choose X hX using fun i j => hCx (x i j)
  exact ⟨incM F (Matrix.of X), mem_ratMx.2 ⟨_, rfl⟩, fun i _ j _ => hX i j⟩

theorem exists_cov (p q : ℕ) : ∃ (ν : Measure (Mx F E p q)) (𝓕 : Set (Mx F E p q)),
    ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratMx F E p q) 𝓕 ν ∧ ν 𝓕 = 1 := by
  obtain ⟨K, hK, hKx⟩ := ratMx_cocompact (F := F) (E := E) p q
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (ratMx F E p q)
  set μ : Measure (Mx F E p q) := Measure.addHaar
  have htop : μ D ≠ ⊤ :=
    (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (ratMx F E p q) hK hKx μ (hD μ)).ne
  have h0 : μ D ≠ 0 := (hD μ).measure_ne_zero (NeZero.ne μ)
  refine ⟨(μ D)⁻¹ • μ, D, ?_, hD _, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

theorem doubled_group_topological_properties (σ : E →ₐ[F] E) {n : ℕ} (Y : Spc F E n) : IsTopologicalGroup (G2 σ Y) ∧ LocallyCompactSpace (G2 σ Y) ∧
    T2Space (G2 σ Y) ∧ SecondCountableTopology (G2 σ Y) := by
  have hσc : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  haveI : LocallyCompactSpace (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n ⊕ Fin n → Fin n ⊕ Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n ⊕ Fin n) (AE F E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n ⊕ Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n ⊕ Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hc : IsClosed (UG (cA σ) (dbl (incM F Y.J)) : Set (GL (Fin n ⊕ Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n ⊕ Fin n) (AE F E) => (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hσc)) continuous_const
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    inferInstanceAs (T2Space (UG (cA σ) (dbl (incM F Y.J)))),
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology⟩

end PositivityTheory.SiegelWeilFormula.kfour

end
