import Mathlib

namespace GroundTheory.LocalField

open IntermediateField

open scoped commutatorElement

section MaximalAbelian

variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]

def commutatorClosure : ClosedSubgroup (Ω ≃ₐ[F] Ω) where
  toSubgroup := (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure
  isClosed' := Subgroup.isClosed_topologicalClosure _

instance normal_commutatorClosure : (commutatorClosure F Ω).Normal :=
  inferInstanceAs (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure.Normal

def maximalAbelianExtension : IntermediateField F Ω :=
  fixedField (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure

variable [IsGalois F Ω]

instance isGalois_maximalAbelianExtension : IsGalois F (maximalAbelianExtension F Ω) :=
  IsGalois.of_fixedField_normal_subgroup _

theorem fixingSubgroup_maximalAbelianExtension :
    (maximalAbelianExtension F Ω).fixingSubgroup = (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure :=
  InfiniteGalois.fixingSubgroup_fixedField (commutatorClosure F Ω)

noncomputable def topologicalAbelianizationEquiv :
    TopologicalAbelianization (Ω ≃ₐ[F] Ω) ≃ₜ*
      (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) :=
  have : T2Space (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) :=
    krullTopology_t2
  let e := InfiniteGalois.normalAutEquivQuotient (commutatorClosure F Ω)
  have hc : Continuous e := by
    apply Continuous.quotient_lift
    exact InfiniteGalois.restrictNormalHom_continuous _
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

theorem topologicalAbelianizationEquiv_mk (σ : Ω ≃ₐ[F] Ω) :
    topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) =
      AlgEquiv.restrictNormalHom (maximalAbelianExtension F Ω) σ :=
  rfl

theorem topologicalAbelianizationEquiv_mk_apply (σ : Ω ≃ₐ[F] Ω) (x : maximalAbelianExtension F Ω) :
    ((topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) x : _) : Ω) =
      σ x := by
  rw [topologicalAbelianizationEquiv_mk, AlgEquiv.restrictNormalHom_apply]

end MaximalAbelian

section Restrict

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem commutator_le_ker_of_comm {G M : Type*} [Group G] [Group M] [IsMulCommutative M]
    (f : G →* M) : commutator G ≤ f.ker := by
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm' _ _

theorem le_maximalAbelianExtension (L : IntermediateField F Ω) [IsAbelianGalois F L] :
    L ≤ maximalAbelianExtension F Ω := by
  have : T2Space (L ≃ₐ[F] L) := krullTopology_t2
  rw [maximalAbelianExtension, le_iff_le, ← L.restrictNormalHom_ker]
  refine Subgroup.topologicalClosure_minimal _ (commutator_le_ker_of_comm _) ?_
  exact isClosed_singleton.preimage (InfiniteGalois.restrictNormalHom_continuous L)

variable (E : IntermediateField F Ω) [Normal F E]

theorem closure_commutator_le_ker_restrictNormalHom (h : E ≤ maximalAbelianExtension F Ω) :
    (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure ≤ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E).ker := by
  rw [E.restrictNormalHom_ker, ← fixingSubgroup_maximalAbelianExtension]
  exact fixingSubgroup_le h

noncomputable def restrictAb (h : E ≤ maximalAbelianExtension F Ω) :
    (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) →* (E ≃ₐ[F] E) :=
  (QuotientGroup.lift _ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E)
    (closure_commutator_le_ker_restrictNormalHom E h)).comp
      (topologicalAbelianizationEquiv F Ω).symm.toMulEquiv.toMonoidHom

theorem restrictAb_topologicalAbelianizationEquiv (h : E ≤ maximalAbelianExtension F Ω) (σ : Ω ≃ₐ[F] Ω) :
    restrictAb E h (topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω))) =
      AlgEquiv.restrictNormalHom E σ := by
  change QuotientGroup.lift _ _ (closure_commutator_le_ker_restrictNormalHom E h)
    ((topologicalAbelianizationEquiv F Ω).symm (topologicalAbelianizationEquiv F Ω _)) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

theorem restrictAb_apply (h : E ≤ maximalAbelianExtension F Ω) (σ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) (x : E) :
    ((restrictAb E h σ x : E) : Ω) = ((σ ⟨x, h x.2⟩ : maximalAbelianExtension F Ω) : Ω) := by
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective ((topologicalAbelianizationEquiv F Ω).symm σ)
  have hσ : σ = topologicalAbelianizationEquiv F Ω (τ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) := by
    rw [hτ, ContinuousMulEquiv.apply_symm_apply]
  rw [hσ, restrictAb_topologicalAbelianizationEquiv, AlgEquiv.restrictNormalHom_apply,
    topologicalAbelianizationEquiv_mk_apply]

theorem continuous_restrictAb (h : E ≤ maximalAbelianExtension F Ω) : Continuous (restrictAb E h) := by
  have h1 : Continuous (QuotientGroup.lift _ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E)
      (closure_commutator_le_ker_restrictNormalHom E h)) :=
    Continuous.quotient_lift (InfiniteGalois.restrictNormalHom_continuous E) _
  exact h1.comp (topologicalAbelianizationEquiv F Ω).symm.continuous

end Restrict

section Finite

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem exists_finite_abelian_mem {y : Ω} (hy : y ∈ maximalAbelianExtension F Ω) :
    ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsAbelianGalois F L ∧ y ∈ L := by
  have : FiniteDimensional F F⟮y⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  set M : IntermediateField F Ω := normalClosure F F⟮y⟯ Ω
  have : FiniteDimensional F M := normalClosure.is_finiteDimensional F F⟮y⟯ Ω
  have : IsGalois F M := IsGalois.normalClosure F F⟮y⟯ Ω
  have hyM : y ∈ M := IntermediateField.le_normalClosure F⟮y⟯ (mem_adjoin_simple_self F y)
  have hMn : M.fixingSubgroup.Normal := by
    rw [← M.restrictNormalHom_ker]; exact MonoidHom.normal_ker _
  set H : Subgroup (Ω ≃ₐ[F] Ω) := M.fixingSubgroup ⊔ commutator (Ω ≃ₐ[F] Ω)
  have : H.Normal := Subgroup.sup_normal _ _
  set A : IntermediateField F Ω := fixedField H
  have hAM : A ≤ M := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup M]
    exact fixedField_le le_sup_left
  have : FiniteDimensional F A :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hAM).toLinearMap
      (IntermediateField.inclusion hAM).injective
  have hfix : ∀ g ∈ H, AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) A g = 1 := by
    intro g hg
    ext x
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply]
    exact (mem_fixedField_iff H (x : Ω)).1 x.2 g hg
  refine ⟨A, inferInstance, { toIsMulCommutative := ⟨⟨fun σ τ => ?_⟩⟩ }, ?_⟩
  · obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := A) (E := Ω) σ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := A) (E := Ω) τ
    have hc := hfix ⁅σ', τ'⁆ (Subgroup.mem_sup_right
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top σ') (Subgroup.mem_top τ')))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · rw [mem_fixedField_iff]
    intro g hg
    have hle : H ≤ MulAction.stabilizer (Ω ≃ₐ[F] Ω) y := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · exact (IntermediateField.mem_fixingSubgroup_iff M g).1 hg y hyM
      · exact (mem_fixedField_iff _ y).1 hy g (Subgroup.le_topologicalClosure _ hg)
    exact hle hg

theorem maximalAbelianExtension_eq_iSup :
    maximalAbelianExtension F Ω =
      ⨆ (L : IntermediateField F Ω) (_ : FiniteDimensional F L) (_ : IsAbelianGalois F L), L := by
  refine le_antisymm (fun y hy => ?_) (iSup_le fun L => iSup_le fun _ => iSup_le fun _ =>
    le_maximalAbelianExtension L)
  obtain ⟨L, hL1, hL2, hyL⟩ := exists_finite_abelian_mem hy
  have hle : L ≤ ⨆ (L : IntermediateField F Ω) (_ : FiniteDimensional F L) (_ : IsAbelianGalois F L), L :=
    le_iSup_of_le L (le_iSup_of_le hL1 (le_iSup_of_le hL2 le_rfl))
  exact hle hyL

theorem ext_restrictAb {σ τ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω}
    (h : ∀ (L : IntermediateField F Ω) [FiniteDimensional F L] [IsAbelianGalois F L],
      restrictAb L (le_maximalAbelianExtension L) σ = restrictAb L (le_maximalAbelianExtension L) τ) :
    σ = τ := by
  ext x
  obtain ⟨L, hL1, hL2, hxL⟩ := exists_finite_abelian_mem x.2
  have := congrArg (fun ρ : L ≃ₐ[F] L => ((ρ ⟨x, hxL⟩ : L) : Ω)) (h L)
  simpa only [restrictAb_apply] using this

end Finite

section Continuity

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem restrictAb_surjective (E : IntermediateField F Ω) [Normal F E]
    (h : E ≤ maximalAbelianExtension F Ω) : Function.Surjective (restrictAb E h) := by
  intro ρ
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) ρ
  exact ⟨_, restrictAb_topologicalAbelianizationEquiv E h τ⟩

variable (F Ω) in

def finiteAbelianExtensions : Set (IntermediateField F Ω) :=
  {L | FiniteDimensional F L ∧ IsAbelianGalois F L}

omit [IsGalois F Ω] in
theorem mem_finiteAbelianExtensions {L : IntermediateField F Ω} :
    L ∈ finiteAbelianExtensions F Ω ↔ FiniteDimensional F L ∧ IsAbelianGalois F L :=
  Iff.rfl

variable (F Ω) in

noncomputable def restrictAbPi (σ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω)
    (L : finiteAbelianExtensions F Ω) : (L : IntermediateField F Ω) ≃ₐ[F] (L : IntermediateField F Ω) :=
  have := L.2.2
  restrictAb (L : IntermediateField F Ω) (le_maximalAbelianExtension (L : IntermediateField F Ω)) σ

theorem continuous_restrictAbPi : Continuous (restrictAbPi F Ω) :=
  continuous_pi fun L => by
    have := L.2.2
    exact continuous_restrictAb _ _

theorem injective_restrictAbPi : Function.Injective (restrictAbPi F Ω) := by
  intro σ τ hστ
  refine ext_restrictAb fun L _ _ => ?_
  exact congrFun hστ ⟨L, inferInstance, inferInstance⟩

theorem isClosedEmbedding_restrictAbPi : Topology.IsClosedEmbedding (restrictAbPi F Ω) := by
  have : ∀ L : finiteAbelianExtensions F Ω,
      T2Space ((L : IntermediateField F Ω) ≃ₐ[F] (L : IntermediateField F Ω)) := fun L => by
    have := L.2.2
    exact krullTopology_t2
  exact continuous_restrictAbPi.isClosedEmbedding injective_restrictAbPi

theorem continuous_iff_restrictAb {X : Type*} [TopologicalSpace X]
    {f : X → maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω} :
    Continuous f ↔ ∀ (L : IntermediateField F Ω) [FiniteDimensional F L] [IsAbelianGalois F L],
      Continuous fun x => restrictAb L (le_maximalAbelianExtension L) (f x) := by
  constructor
  · intro hf L _ _
    exact (continuous_restrictAb _ _).comp hf
  · intro h
    rw [isClosedEmbedding_restrictAbPi.isInducing.continuous_iff, continuous_pi_iff]
    intro L
    have := L.2.1
    have := L.2.2
    exact h (L : IntermediateField F Ω)

end Continuity

section Commutative

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

instance isMulCommutative_maximalAbelianExtension :
    IsMulCommutative (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) :=
  ⟨⟨fun σ τ => (topologicalAbelianizationEquiv F Ω).symm.injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩

theorem isAbelianGalois_of_le_maximalAbelianExtension (E : IntermediateField F Ω) [Normal F E]
    (h : E ≤ maximalAbelianExtension F Ω) : IsAbelianGalois F E := by
  have : IsGalois F E :=
    have := Algebra.isSeparable_tower_bot_of_isSeparable F E Ω
    IsGalois.mk
  refine { toIsMulCommutative := ⟨⟨fun σ τ => ?_⟩⟩ }
  obtain ⟨σ', rfl⟩ := restrictAb_surjective E h σ
  obtain ⟨τ', rfl⟩ := restrictAb_surjective E h τ
  rw [← map_mul, ← map_mul, mul_comm' σ' τ']

theorem isAbelianGalois_iff_le_maximalAbelianExtension (E : IntermediateField F Ω) [Normal F E] :
    IsAbelianGalois F E ↔ E ≤ maximalAbelianExtension F Ω :=
  ⟨fun _ => le_maximalAbelianExtension E, isAbelianGalois_of_le_maximalAbelianExtension E⟩

end Commutative

end GroundTheory.LocalField
