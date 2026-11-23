import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftCoactionIffIsCoactionComm
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv

namespace GlobalTheory

section Comodule

open CartierDual

variable {R C M M' : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

def dualContraction (ρ : M →ₗ[R] M ⊗[R] C) : CartierDual R C →ₗ[R] Module.End R M :=
  (tensorToHom R M C ∘ₗ ρ).flip

theorem dualContraction_apply (ρ : M →ₗ[R] M ⊗[R] C) (w : CartierDual R C) (m : M) :
    dualContraction ρ w m = tensorToHom R M C (ρ m) w := rfl

theorem dualContraction_eq_rid (ρ : M →ₗ[R] M ⊗[R] C) (w : CartierDual R C) (m : M) :
    dualContraction ρ w m = TensorProduct.rid R M (w.ofConv.lTensor M (ρ m)) :=
  tensorToHom_apply _ _

variable (R M C) in

def dualContractionEquiv [Module.Finite R C] [Module.Projective R C] :
    (M →ₗ[R] M ⊗[R] C) ≃ (CartierDual R C →ₗ[R] Module.End R M) where
  toFun := dualContraction
  invFun θ := (tensorEquivHom R M C).symm.toLinearMap ∘ₗ θ.flip
  left_inv ρ := LinearMap.ext fun m => (tensorEquivHom R M C).symm_apply_apply (ρ m)
  right_inv θ := LinearMap.ext fun w => LinearMap.ext fun m =>
    congr($((tensorEquivHom R M C).apply_symm_apply (θ.flip m)) w)

@[simp] theorem dualContractionEquiv_apply [Module.Finite R C] [Module.Projective R C]
    (ρ : M →ₗ[R] M ⊗[R] C) : dualContractionEquiv R C M ρ = dualContraction ρ := rfl

theorem dualContraction_of_mem_coactionWeightSpace {ρ : M →ₗ[R] M ⊗[R] C} {g : C} {m : M}
    (hm : m ∈ coactionWeightSpace ρ g) (w : CartierDual R C) :
    dualContraction ρ w m = w g • m := by
  rw [dualContraction_apply, mem_coactionWeightSpace.1 hm, tensorToHom_tmul]

theorem mem_coactionWeightSpace_iff_dualContraction [Module.Finite R C] [Module.Projective R C]
    {ρ : M →ₗ[R] M ⊗[R] C} {g : C} {m : M} :
    m ∈ coactionWeightSpace ρ g ↔ ∀ w : CartierDual R C, dualContraction ρ w m = w g • m :=
  ⟨dualContraction_of_mem_coactionWeightSpace, fun h => eq_of_forall_tensorToHom h⟩

private theorem tensorToHom_rTensor (f : M →ₗ[R] M') (x : M ⊗[R] C) (w : CartierDual R C) :
    tensorToHom R M' C (f.rTensor C x) w = f (tensorToHom R M C x w) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul n m => simp

theorem dualContraction_map {ρ : M →ₗ[R] M ⊗[R] C} {ρ' : M' →ₗ[R] M' ⊗[R] C} {f : M →ₗ[R] M'}
    (hf : ∀ m, ρ' (f m) = f.rTensor C (ρ m)) (w : CartierDual R C) (m : M) :
    dualContraction ρ' w (f m) = f (dualContraction ρ w m) := by
  rw [dualContraction_apply, hf, tensorToHom_rTensor, dualContraction_apply]

theorem comm_iff_dualContraction_map [Module.Finite R C] [Module.Projective R C]
    {ρ : M →ₗ[R] M ⊗[R] C} {ρ' : M' →ₗ[R] M' ⊗[R] C} {f : M →ₗ[R] M'} :
    (∀ m, ρ' (f m) = f.rTensor C (ρ m)) ↔
      ∀ (w : CartierDual R C) (m : M), dualContraction ρ' w (f m) = f (dualContraction ρ w m) :=
  ⟨dualContraction_map, fun h m => eq_of_forall_tensorToHom fun w => by
    rw [tensorToHom_rTensor]; exact h w m⟩

variable [Coalgebra R C]

private theorem tensorToHom_assoc_rTensor (ρ : M →ₗ[R] M ⊗[R] C) (φ ψ : CartierDual R C)
    (x : M ⊗[R] C) :
    tensorToHom R M (C ⊗[R] C) (TensorProduct.assoc R M C C (ρ.rTensor C x))
      (toConv (pair R C C (φ ⊗ₜ ψ))) = dualContraction ρ φ (tensorToHom R M C x ψ) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul m c =>
    rw [LinearMap.rTensor_tmul, tensorToHom_tmul, map_smul, dualContraction_apply]
    generalize ρ m = s
    induction s with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, add_tmul, smul_add, hx, hy]
    | tmul m' c' => simp [smul_smul, mul_comm]

private theorem tensorToHom_lTensor_comul (φ ψ : CartierDual R C) (x : M ⊗[R] C) :
    tensorToHom R M (C ⊗[R] C) ((comul : C →ₗ[R] C ⊗[R] C).lTensor M x)
      (toConv (pair R C C (φ ⊗ₜ ψ))) = tensorToHom R M C x (φ * ψ) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul m c => rw [LinearMap.lTensor_tmul, tensorToHom_tmul, tensorToHom_tmul, mul_apply]

theorem IsCoaction.dualContraction_one {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) :
    dualContraction ρ 1 = 1 :=
  LinearMap.ext fun m => (dualContraction_eq_rid ρ 1 m).trans (h.rid_counit m)

theorem IsCoaction.dualContraction_mul {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ)
    (φ ψ : CartierDual R C) :
    dualContraction ρ (φ * ψ) = dualContraction ρ φ * dualContraction ρ ψ :=
  LinearMap.ext fun m => by
    rw [Module.End.mul_apply, dualContraction_apply, dualContraction_apply ρ ψ,
      ← tensorToHom_lTensor_comul, ← h.coassoc, tensorToHom_assoc_rTensor]

theorem isCoaction_iff_dualContraction [Module.Finite R C] [Module.Projective R C]
    {ρ : M →ₗ[R] M ⊗[R] C} :
    IsCoaction ρ ↔ dualContraction ρ 1 = 1 ∧
      ∀ φ ψ, dualContraction ρ (φ * ψ) = dualContraction ρ φ * dualContraction ρ ψ := by
  refine ⟨fun h => ⟨h.dualContraction_one, h.dualContraction_mul⟩, fun ⟨h1, h2⟩ =>
    ⟨fun m => eq_of_forall_tensorToHom_pair fun φ ψ => ?_, fun m => ?_⟩⟩
  · rw [tensorToHom_lTensor_comul, tensorToHom_assoc_rTensor]
    exact congr($(h2 φ ψ) m).symm
  · refine (TensorProduct.rid R M).injective ?_
    rw [TensorProduct.rid_tmul, one_smul]
    exact (dualContraction_eq_rid ρ 1 m).symm.trans congr($h1 m)

def IsCoaction.dualAction {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) :
    CartierDual R C →ₐ[R] Module.End R M :=
  AlgHom.ofLinearMap (dualContraction ρ) h.dualContraction_one h.dualContraction_mul

@[simp] theorem IsCoaction.dualAction_apply {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ)
    (w : CartierDual R C) : h.dualAction w = dualContraction ρ w := rfl

abbrev IsCoaction.dualModule {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) :
    Module (CartierDual R C) M :=
  Module.compHom M h.dualAction.toRingHom

theorem IsCoaction.dualModule_smul {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ)
    (w : CartierDual R C) (m : M) : letI := h.dualModule; w • m = dualContraction ρ w m := rfl

theorem IsCoaction.dualModule_isScalarTower {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) :
    letI := h.dualModule; IsScalarTower R (CartierDual R C) M :=
  letI := h.dualModule
  ⟨fun r w m => congr($((dualContraction ρ).map_smul r w) m)⟩

variable (R C M) in

def coactionEquivDualAction [Module.Finite R C] [Module.Projective R C] :
    {ρ : M →ₗ[R] M ⊗[R] C // IsCoaction ρ} ≃ (CartierDual R C →ₐ[R] Module.End R M) where
  toFun ρ := ρ.2.dualAction
  invFun θ := ⟨(dualContractionEquiv R C M).symm θ.toLinearMap, by
    rw [isCoaction_iff_dualContraction, ← dualContractionEquiv_apply, Equiv.apply_symm_apply]
    exact ⟨map_one θ, map_mul θ⟩⟩
  left_inv ρ := Subtype.ext ((dualContractionEquiv R C M).symm_apply_apply ρ.1)
  right_inv θ := AlgHom.toLinearMap_injective
    ((dualContractionEquiv R C M).apply_symm_apply θ.toLinearMap)

@[simp] theorem coactionEquivDualAction_apply [Module.Finite R C] [Module.Projective R C]
    (ρ : {ρ : M →ₗ[R] M ⊗[R] C // IsCoaction ρ}) :
    coactionEquivDualAction R C M ρ = ρ.2.dualAction := rfl

theorem existsUnique_isCoaction_of_module [Module.Finite R C] [Module.Projective R C]
    [Module (CartierDual R C) M] [IsScalarTower R (CartierDual R C) M] :
    ∃! ρ : M →ₗ[R] M ⊗[R] C, IsCoaction ρ ∧
      ∀ (w : CartierDual R C) (m : M), dualContraction ρ w m = w • m := by
  let θ : CartierDual R C →ₐ[R] Module.End R M := Algebra.lsmul R R M
  refine ⟨((coactionEquivDualAction R C M).symm θ).1,
    ⟨((coactionEquivDualAction R C M).symm θ).2, fun w m =>
      congr($((coactionEquivDualAction R C M).apply_symm_apply θ) w m)⟩, fun ρ hρ => ?_⟩
  have : coactionEquivDualAction R C M ⟨ρ, hρ.1⟩ = θ :=
    AlgHom.ext fun w => LinearMap.ext fun m => hρ.2 w m
  rw [← this, Equiv.symm_apply_apply]

end Comodule

section Augmented

variable {R : Type*} [CommRing R]

section Noncommutative

variable {D : Type*} [Ring D] [Algebra R D] {M : Type*} [AddCommGroup M] [Module R M] [Module D M]
  [IsScalarTower R D M]

theorem forall_ker_smul_eq_zero_iff (ε : D →ₐ[R] R) (m : M) :
    (∀ w ∈ RingHom.ker ε, w • m = 0) ↔ ∀ w : D, w • m = ε w • m := by
  refine ⟨fun h w => ?_, fun h w hw => by rw [h, RingHom.mem_ker.1 hw, zero_smul]⟩
  have := h (w - algebraMap R D (ε w)) (by simp [RingHom.mem_ker])
  rwa [sub_smul, algebraMap_smul, sub_eq_zero] at this

theorem forall_ker_mul_eq_zero_iff (ε : D →ₐ[R] R) (Λ : D) :
    (∀ w ∈ RingHom.ker ε, w * Λ = 0) ↔ ∀ w : D, w * Λ = ε w • Λ :=
  forall_ker_smul_eq_zero_iff ε Λ

theorem smul_smul_eq_of_forall_ker_mul_eq_zero {ε : D →ₐ[R] R} {Λ : D}
    (hΛ : ∀ w ∈ RingHom.ker ε, w * Λ = 0) (m : M) (w : D) : w • Λ • m = ε w • Λ • m := by
  rw [← mul_smul, (forall_ker_mul_eq_zero_iff ε Λ).1 hΛ, smul_assoc]

end Noncommutative

variable {D D' : Type*} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']

theorem mem_annihilator_iff_forall_mul {I : Ideal D} {Λ : D} :
    Λ ∈ I.annihilator ↔ ∀ w ∈ I, w * Λ = 0 := by
  simp only [Submodule.mem_annihilator, smul_eq_mul, mul_comm Λ]

theorem mem_annihilator_ker_iff {ε : D →ₐ[R] R} {Λ : D} :
    Λ ∈ (RingHom.ker ε).annihilator ↔ ∀ w : D, w * Λ = ε w • Λ :=
  mem_annihilator_iff_forall_mul.trans (forall_ker_mul_eq_zero_iff ε Λ)

theorem smul_smul_eq_of_mem_annihilator_ker {M : Type*} [AddCommGroup M] [Module R M] [Module D M]
    [IsScalarTower R D M] {ε : D →ₐ[R] R} {Λ : D} (hΛ : Λ ∈ (RingHom.ker ε).annihilator) (m : M)
    (w : D) : w • Λ • m = ε w • Λ • m :=
  smul_smul_eq_of_forall_ker_mul_eq_zero (mem_annihilator_iff_forall_mul.1 hΛ) m w

theorem smul_eq_smul_of_mem_annihilator_ker {ε : D →ₐ[R] R} {Λ T : D}
    (hΛ : Λ ∈ (RingHom.ker ε).annihilator) (hT : T ∈ (RingHom.ker ε).annihilator) :
    ε Λ • T = ε T • Λ := by
  rw [← mem_annihilator_ker_iff.1 hT, ← mem_annihilator_ker_iff.1 hΛ, mul_comm]

theorem map_mem_annihilator_ker_iff {ε : D →ₐ[R] R} {ε' : D' →ₐ[R] R} (e : D ≃ₐ[R] D')
    (he : ∀ d, ε' (e d) = ε d) {Λ : D} :
    e Λ ∈ (RingHom.ker ε').annihilator ↔ Λ ∈ (RingHom.ker ε).annihilator := by
  simp only [mem_annihilator_ker_iff]
  rw [e.surjective.forall]
  refine forall_congr' fun w => ?_
  rw [← map_mul, he, ← map_smul, e.injective.eq_iff]

theorem prod_mk_zero_mem_annihilator_ker_iff {ε : D →ₐ[R] R} {Λ : D} :
    ((Λ, 0) : D × D') ∈ (RingHom.ker (ε.comp (AlgHom.fst R D D'))).annihilator ↔
      Λ ∈ (RingHom.ker ε).annihilator := by
  simp [mem_annihilator_ker_iff]

theorem pi_single_mem_annihilator_ker_iff {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] {i : ι} {ε : A i →ₐ[R] R} {Λ : A i} :
    Pi.single i Λ ∈ (RingHom.ker (ε.comp (Pi.evalAlgHom R A i))).annihilator ↔
      Λ ∈ (RingHom.ker ε).annihilator := by
  simp only [mem_annihilator_ker_iff]
  refine ⟨fun h w => by simpa using congrFun (h (Pi.single i w)) i, fun h w => funext fun j => ?_⟩
  by_cases hj : j = i
  · subst hj; simpa using h (w j)
  · simp [hj]

theorem sum_mem_annihilator_ker {G : Type*} [Group G] [Fintype G] {ε : D →ₐ[R] R} (y : G →* D)
    (hy : ∀ g, ε (y g) = 1) (hspan : Submodule.span R (Set.range y) = ⊤) :
    ∑ g, y g ∈ (RingHom.ker ε).annihilator ∧ ε (∑ g, y g) = Fintype.card G := by
  refine ⟨mem_annihilator_ker_iff.2 fun w => ?_, by simp [hy]⟩
  have hw : w ∈ Submodule.span R (Set.range y) := hspan ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [hy, one_smul, Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun g' => by simp
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul, ha, hb, map_add, add_smul]
  | smul r a _ ha => rw [smul_mul_assoc, ha, map_smul, smul_assoc]

end Augmented

section Invariants

variable {R H M : Type*} [CommRing R] [Semiring H] [Bialgebra R H] [Module.Finite R H]
  [Module.Projective R H] [AddCommGroup M] [Module R M]

theorem counitAlgHom_cartierDual_apply (w : CartierDual R H) :
    counitAlgHom R (CartierDual R H) w = w 1 := rfl

theorem invariant_iff_dualContraction {ρ : M →ₗ[R] M ⊗[R] H} {m : M} :
    ρ m = m ⊗ₜ 1 ↔ ∀ w : CartierDual R H, dualContraction ρ w m = w 1 • m :=
  mem_coactionWeightSpace_iff_dualContraction

theorem IsCoaction.invariant_iff_forall_ker {ρ : M →ₗ[R] M ⊗[R] H} (h : IsCoaction ρ) {m : M} :
    ρ m = m ⊗ₜ 1 ↔
      ∀ w ∈ RingHom.ker (counitAlgHom R (CartierDual R H)), dualContraction ρ w m = 0 :=
  letI := h.dualModule
  haveI := h.dualModule_isScalarTower
  invariant_iff_dualContraction.trans
    (forall_ker_smul_eq_zero_iff (counitAlgHom R (CartierDual R H)) m).symm

theorem IsCoaction.invariant_dualContraction {ρ : M →ₗ[R] M ⊗[R] H} (h : IsCoaction ρ)
    {Λ : CartierDual R H} (hΛ : ∀ w ∈ RingHom.ker (counitAlgHom R (CartierDual R H)), w * Λ = 0)
    (m : M) : ρ (dualContraction ρ Λ m) = dualContraction ρ Λ m ⊗ₜ 1 :=
  h.invariant_iff_forall_ker.2 fun w hw => by
    rw [← Module.End.mul_apply, ← h.dualContraction_mul, hΛ w hw, map_zero, LinearMap.zero_apply]

theorem IsCoaction.invariant_dualContraction_of_mem_annihilator [IsCocomm R H]
    {ρ : M →ₗ[R] M ⊗[R] H} (h : IsCoaction ρ) {Λ : CartierDual R H}
    (hΛ : Λ ∈ (RingHom.ker (counitAlgHom R (CartierDual R H))).annihilator) (m : M) :
    ρ (dualContraction ρ Λ m) = dualContraction ρ Λ m ⊗ₜ 1 :=
  h.invariant_dualContraction (mem_annihilator_iff_forall_mul.1 hΛ) m

theorem dualContraction_of_invariant {ρ : M →ₗ[R] M ⊗[R] H} {m : M} (hm : ρ m = m ⊗ₜ 1)
    (Λ : CartierDual R H) : dualContraction ρ Λ m = Λ 1 • m :=
  invariant_iff_dualContraction.1 hm Λ

end Invariants

section Unramified

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem isIdempotentElem_of_mem_annihilator_ker {ε : A →ₐ[R] R} {e : A}
    (he : e ∈ (RingHom.ker ε).annihilator) (he1 : ε e = 1) : IsIdempotentElem e := by
  rw [IsIdempotentElem, mem_annihilator_ker_iff.1 he, he1, one_smul]

theorem eq_smul_of_mem_annihilator_ker {ε : A →ₐ[R] R} {e Λ : A}
    (he : e ∈ (RingHom.ker ε).annihilator) (he1 : ε e = 1)
    (hΛ : Λ ∈ (RingHom.ker ε).annihilator) : Λ = ε Λ • e := by
  rw [← smul_eq_smul_of_mem_annihilator_ker he hΛ, he1, one_smul]

theorem ker_eq_span_one_sub {ε : A →ₐ[R] R} {e : A}
    (he : e ∈ (RingHom.ker ε).annihilator) (he1 : ε e = 1) :
    RingHom.ker ε = Ideal.span {1 - e} := by
  refine le_antisymm (fun w hw => Ideal.mem_span_singleton'.2 ⟨w, ?_⟩) ?_
  · rw [mul_sub, mul_one, mem_annihilator_iff_forall_mul.1 he w hw, sub_zero]
  · simp [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, he1]

theorem annihilator_ker_eq_span {ε : A →ₐ[R] R} {e : A}
    (he : e ∈ (RingHom.ker ε).annihilator) (he1 : ε e = 1) :
    (RingHom.ker ε).annihilator = Ideal.span {e} := by
  refine le_antisymm (fun Λ hΛ => Ideal.mem_span_singleton'.2 ⟨algebraMap R A (ε Λ), ?_⟩)
    ((Ideal.span_singleton_le_iff_mem _).2 he)
  rw [← Algebra.smul_def, ← eq_smul_of_mem_annihilator_ker he he1 hΛ]

theorem annihilator_ker_restrictScalars_eq_span {ε : A →ₐ[R] R} {e : A}
    (he : e ∈ (RingHom.ker ε).annihilator) (he1 : ε e = 1) :
    (RingHom.ker ε).annihilator.restrictScalars R = R ∙ e := by
  refine le_antisymm (fun Λ hΛ => Submodule.mem_span_singleton.2 ⟨ε Λ, ?_⟩)
    ((Submodule.span_singleton_le_iff_mem _ _).2 he)
  exact (eq_smul_of_mem_annihilator_ker he he1 hΛ).symm

theorem bijective_prod_quotient_of_mem_annihilator_ker {ε : A →ₐ[R] R} {e : A}
    (he : e ∈ (RingHom.ker ε).annihilator) (he1 : ε e = 1) :
    Function.Bijective (ε.prod (Ideal.Quotient.mkₐ R (Ideal.span {e}))) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun ⟨r, q⟩ => ?_⟩
  · have h1 : ε a = 0 := congrArg Prod.fst ha
    have h2 : a ∈ Ideal.span {e} := Ideal.Quotient.eq_zero_iff_mem.1 (congrArg Prod.snd ha)
    rw [← annihilator_ker_eq_span he he1] at h2
    rw [eq_smul_of_mem_annihilator_ker he he1 h2, h1, zero_smul]
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h0 : Ideal.Quotient.mkₐ R (Ideal.span {e}) e = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self e)
    refine ⟨a + (r - ε a) • e, Prod.ext ?_ ?_⟩
    · simp [he1]
    · change Ideal.Quotient.mkₐ R (Ideal.span {e}) (a + (r - ε a) • e) = _
      rw [map_add, map_smul, h0, smul_zero, add_zero]; rfl

theorem existsUnique_mem_annihilator_ker [Algebra.FormallyUnramified R A]
    [Algebra.EssFiniteType R A] (ε : A →ₐ[R] R) :
    ∃! e, e ∈ (RingHom.ker ε).annihilator ∧ ε e = 1 := by
  let π : A ⊗[R] A →ₐ[R] A := Algebra.TensorProduct.lift ((Algebra.ofId R A).comp ε) (AlgHom.id R A)
    fun _ _ => Commute.all _ _
  have hπ (t : A ⊗[R] A) : ε (π t) = ε (Algebra.TensorProduct.lmul' R t) := by
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b => simp [π, Algebra.ofId_apply]
  have he : π (Algebra.FormallyUnramified.elem R A) ∈ (RingHom.ker ε).annihilator :=
    mem_annihilator_ker_iff.2 fun w => by
      have := congrArg π (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) w)
      simpa [π, Algebra.ofId_apply, Algebra.smul_def] using this
  have he1 : ε (π (Algebra.FormallyUnramified.elem R A)) = 1 := by
    rw [hπ, Algebra.FormallyUnramified.lmul_elem, map_one]
  refine ⟨_, ⟨he, he1⟩, fun e' he' => ?_⟩
  rw [eq_smul_of_mem_annihilator_ker he he1 he'.1, he'.2, one_smul]

theorem finrank_annihilator_ker {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [Algebra.FormallyUnramified K A] [Algebra.EssFiniteType K A] (ε : A →ₐ[K] K) :
    Module.finrank K ((RingHom.ker ε).annihilator.restrictScalars K) = 1 := by
  obtain ⟨e, ⟨he, he1⟩, -⟩ := existsUnique_mem_annihilator_ker ε
  rw [annihilator_ker_restrictScalars_eq_span he he1]
  exact finrank_span_singleton fun h => by simp [h] at he1

end Unramified

section BaseChange

variable {R D : Type*} (K : Type*) [CommRing R] [CommRing D] [Algebra R D] [CommRing K]
  [Algebra R K]

def augmentationBaseChange (ε : D →ₐ[R] R) : K ⊗[R] D →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp ε) fun _ _ => Commute.all _ _

@[simp] theorem augmentationBaseChange_tmul (ε : D →ₐ[R] R) (k : K) (d : D) :
    augmentationBaseChange K ε (k ⊗ₜ d) = k * algebraMap R K (ε d) := rfl

variable {K}

theorem eq_augmentationBaseChange {ε : D →ₐ[R] R} {ε' : K ⊗[R] D →ₐ[K] K}
    (h : ∀ d, ε' (1 ⊗ₜ d) = algebraMap R K (ε d)) : ε' = augmentationBaseChange K ε :=
  Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun d => by simpa using h d)

theorem counitAlgHom_baseChange (H : Type*) [CommRing H] [Bialgebra R H] :
    counitAlgHom K (K ⊗[R] H) = augmentationBaseChange K (counitAlgHom R H) :=
  eq_augmentationBaseChange fun d => by simp [Algebra.smul_def]

variable (K) in

theorem one_tmul_mem_annihilator_ker {ε : D →ₐ[R] R} {Λ : D}
    (hΛ : Λ ∈ (RingHom.ker ε).annihilator) :
    (1 : K) ⊗ₜ[R] Λ ∈ (RingHom.ker (augmentationBaseChange K ε)).annihilator := by
  refine mem_annihilator_ker_iff.2 fun w => ?_
  induction w with
  | zero => simp
  | add a b ha hb => rw [add_mul, ha, hb, map_add, add_smul]
  | tmul k d =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mem_annihilator_ker_iff.1 hΛ,
      augmentationBaseChange_tmul, smul_tmul', ← smul_tmul]
    simp [Algebra.smul_def, mul_comm]

theorem one_tmul_mem_annihilator_ker_iff (hD : Function.Injective fun d : D => (1 : K) ⊗ₜ[R] d)
    {ε : D →ₐ[R] R} {Λ : D} :
    (1 : K) ⊗ₜ[R] Λ ∈ (RingHom.ker (augmentationBaseChange K ε)).annihilator ↔
      Λ ∈ (RingHom.ker ε).annihilator := by
  refine ⟨fun h => mem_annihilator_iff_forall_mul.2 fun w hw => hD ?_,
    one_tmul_mem_annihilator_ker K⟩
  have := mem_annihilator_iff_forall_mul.1 h (1 ⊗ₜ w)
    (by simp [RingHom.mem_ker, RingHom.mem_ker.1 hw])
  simpa using this

theorem smul_eq_smul_one_tmul {ε : D →ₐ[R] R} {Λ : D} (hΛ : Λ ∈ (RingHom.ker ε).annihilator)
    {T : K ⊗[R] D} (hT : T ∈ (RingHom.ker (augmentationBaseChange K ε)).annihilator) :
    algebraMap R K (ε Λ) • T = augmentationBaseChange K ε T • (1 : K) ⊗ₜ[R] Λ := by
  simpa using smul_eq_smul_of_mem_annihilator_ker (one_tmul_mem_annihilator_ker K hΛ) hT

theorem eq_div_smul_one_tmul {K : Type*} [Field K] [Algebra R K] {ε : D →ₐ[R] R} {Λ : D}
    (hΛ : Λ ∈ (RingHom.ker ε).annihilator) (h0 : algebraMap R K (ε Λ) ≠ 0)
    {T : K ⊗[R] D} (hT : T ∈ (RingHom.ker (augmentationBaseChange K ε)).annihilator) :
    T = (augmentationBaseChange K ε T / algebraMap R K (ε Λ)) • (1 : K) ⊗ₜ[R] Λ := by
  rw [div_eq_inv_mul, mul_smul, ← smul_eq_smul_one_tmul hΛ hT, inv_smul_smul₀ h0]

open nonZeroDivisors in

theorem one_tmul_injective_of_isTorsionFree (K : Type*) [Field K] [IsDomain R] [Algebra R K]
    [IsFractionRing R K] (M : Type*) [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] :
    Function.Injective fun m : M => (1 : K) ⊗ₜ[R] m :=
  (IsLocalizedModule.injective_iff_isRegular R⁰ (TensorProduct.mk R K M 1)).2 fun c =>
    IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero c.2)

end BaseChange

section GenericFibre

variable {R D : Type*} [CommRing R] [CommRing D] [Algebra R D]
  (K : Type*) [Field K] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  [Module.IsTorsionFree R D] [Algebra.FormallyUnramified K (K ⊗[R] D)]
  [Algebra.EssFiniteType K (K ⊗[R] D)]

include K in

theorem eq_zero_of_mem_annihilator_ker {ε : D →ₐ[R] R} {Λ : D}
    (hΛ : Λ ∈ (RingHom.ker ε).annihilator) (h0 : ε Λ = 0) : Λ = 0 := by
  obtain ⟨e, ⟨he, he1⟩, -⟩ := existsUnique_mem_annihilator_ker (augmentationBaseChange K ε)
  refine one_tmul_injective_of_isTorsionFree (R := R) K D ?_
  simpa [h0] using eq_smul_of_mem_annihilator_ker he he1 (one_tmul_mem_annihilator_ker K hΛ)

open nonZeroDivisors in
include K in

theorem exists_mem_annihilator_ker_ne_zero (ε : D →ₐ[R] R) :
    ∃ Λ ∈ (RingHom.ker ε).annihilator, ε Λ ≠ 0 := by
  obtain ⟨e, ⟨he, he1⟩, -⟩ := existsUnique_mem_annihilator_ker (augmentationBaseChange K ε)
  obtain ⟨⟨Λ, s⟩, hs⟩ := IsLocalizedModule.surj R⁰ (TensorProduct.mk R K D 1) e
  have hs' : algebraMap R K s • e = (1 : K) ⊗ₜ[R] Λ := by
    rw [algebraMap_smul]; exact hs
  refine ⟨Λ, (one_tmul_mem_annihilator_ker_iff (one_tmul_injective_of_isTorsionFree K D)).1 ?_,
    fun h => ?_⟩
  · rw [← hs']
    exact Submodule.smul_of_tower_mem _ _ he
  · have := congrArg (augmentationBaseChange K ε) hs'
    rw [map_smul, he1] at this
    simp [h, nonZeroDivisors.ne_zero s.2] at this

end GenericFibre

section ComoduleBaseChange

open CartierDual

variable {R K H M M' : Type*} [CommRing R] [CommRing K] [Algebra R K] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [Module K M'] [IsScalarTower R K M']

theorem dualContraction_baseChange [AddCommMonoid H] [Module R H] {ρ : M →ₗ[R] M ⊗[R] H}
    {ρ' : M' →ₗ[K] M' ⊗[K] (K ⊗[R] H)} {j : M →ₗ[R] M'}
    (hj : ∀ m, AlgebraTensorModule.cancelBaseChange R K K M' H (ρ' (j m)) = j.rTensor H (ρ m))
    (w : CartierDual R H) (m : M) :
    dualContraction ρ' (baseChangeLinear R K H (1 ⊗ₜ w)) (j m) = j (dualContraction ρ w m) := by
  rw [dualContraction_apply, dualContraction_apply, (LinearEquiv.eq_symm_apply _).2 (hj m)]
  generalize ρ m = x
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul n h => simp

variable [Semiring H] [Bialgebra R H] [Module.Finite R H] [Module.Projective R H] [IsCocomm R H]

theorem baseChange_one_tmul_mem_annihilator_ker {Λ : CartierDual R H}
    (hΛ : Λ ∈ (RingHom.ker (counitAlgHom R (CartierDual R H))).annihilator) :
    baseChangeLinear R K H (1 ⊗ₜ Λ) ∈
      (RingHom.ker (counitAlgHom K (CartierDual K (K ⊗[R] H)))).annihilator := by
  refine mem_annihilator_ker_iff.2 fun w => ?_
  obtain ⟨x, rfl⟩ := (baseChangeLinear_bijective K (R := R) (M := H)).2 w
  rw [counitAlgHom_cartierDual_apply, ← baseChangeLinear_mul, ← map_smul]
  congr 1
  induction x with
  | zero => simp
  | add a b ha hb => rw [add_mul, ha, hb, map_add, ofConv_add, LinearMap.add_apply, add_smul]
  | tmul k d =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mem_annihilator_ker_iff.1 hΛ,
      counitAlgHom_cartierDual_apply, Algebra.TensorProduct.one_def, baseChangeLinear_tmul_tmul,
      smul_tmul', ← smul_tmul]
    simp

theorem smul_dualContraction_baseChange {ρ : M →ₗ[R] M ⊗[R] H}
    {ρ' : M' →ₗ[K] M' ⊗[K] (K ⊗[R] H)} {j : M →ₗ[R] M'}
    (hj : ∀ m, AlgebraTensorModule.cancelBaseChange R K K M' H (ρ' (j m)) = j.rTensor H (ρ m))
    {Λ : CartierDual R H} (hΛ : Λ ∈ (RingHom.ker (counitAlgHom R (CartierDual R H))).annihilator)
    {T : CartierDual K (K ⊗[R] H)}
    (hT : T ∈ (RingHom.ker (counitAlgHom K (CartierDual K (K ⊗[R] H)))).annihilator) (m : M) :
    Λ 1 • dualContraction ρ' T (j m) = T 1 • j (dualContraction ρ Λ m) := by
  have h1 : baseChangeLinear R K H (1 ⊗ₜ Λ) 1 = algebraMap R K (Λ 1) := by
    rw [Algebra.TensorProduct.one_def, baseChangeLinear_tmul_tmul]
    simp [Algebra.smul_def]
  have h : algebraMap R K (Λ 1) • T = T 1 • baseChangeLinear R K H (1 ⊗ₜ Λ) :=
    h1 ▸ smul_eq_smul_of_mem_annihilator_ker (R := K) (D := CartierDual K (K ⊗[R] H))
      (ε := counitAlgHom K (CartierDual K (K ⊗[R] H)))
      (baseChange_one_tmul_mem_annihilator_ker (K := K) hΛ) hT
  have h2 := congrArg (fun w => dualContraction ρ' w (j m)) h
  simp only [map_smul, LinearMap.smul_apply, dualContraction_baseChange hj] at h2
  rwa [algebraMap_smul] at h2

end ComoduleBaseChange

section Cramer

open Matrix

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem det_mul_eq_zero_of_sum_mul_eq_zero {D : Type*} [CommRing D] {a : Matrix σ σ D} {x : σ → D}
    (h : ∀ i, ∑ j, a i j * x j = 0) (j : σ) : a.det * x j = 0 := by
  have h0 : a *ᵥ x = 0 := funext h
  have h1 : a.adjugate *ᵥ (a *ᵥ x) = a.det • x := by
    rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  rw [h0, mulVec_zero] at h1
  exact (congrFun h1 j).symm

theorem det_mem_annihilator_span {D : Type*} [CommRing D] {a : Matrix σ σ D} {x : σ → D}
    (h : ∀ i, ∑ j, a i j * x j = 0) : a.det ∈ (Ideal.span (Set.range x)).annihilator :=
  (Submodule.mem_annihilator_span _ _).2 fun ⟨_, j, hj⟩ =>
    hj ▸ det_mul_eq_zero_of_sum_mul_eq_zero h j

open MvPowerSeries

variable {R : Type*} [CommRing R]

omit [DecidableEq σ] in

theorem exists_matrix_eq_sum_mul_X {τ : Type*} {f : τ → MvPowerSeries σ R}
    (hf : ∀ i, constantCoeff (f i) = 0) :
    ∃ a : Matrix τ σ (MvPowerSeries σ R), ∀ i, f i = ∑ j, a i j * X j := by
  have h (i) : ∃ c : σ → MvPowerSeries σ R, f i = ∑ j, c j * X j := by
    have : f i ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) :=
      germIdeal_eq_span (σ := σ) (R := R) ▸ hf i
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 this
    exact ⟨c, hc.symm⟩
  choose a ha using h
  exact ⟨a, ha⟩

omit [DecidableEq σ] in

theorem coeff_single_sum_mul_X (c : σ → MvPowerSeries σ R) (j : σ) :
    coeff (Finsupp.single j 1) (∑ l, c l * X l) = constantCoeff (c j) := by
  classical
  rw [map_sum, Finset.sum_eq_single j]
  · have := coeff_add_mul_monomial (0 : σ →₀ ℕ) (Finsupp.single j 1) (c j) 1
    rwa [zero_add, mul_one, ← X_def, coeff_zero_eq_constantCoeff_apply] at this
  · intro l _ hl
    exact X_dvd_iff.1 (dvd_mul_left (X l) (c l)) _ (Finsupp.single_eq_of_ne hl)
  · simp

variable {D : Type*} [CommRing D] [Algebra R D]

omit [DecidableEq σ] in

theorem ker_eq_span_range_X {π : MvPowerSeries σ R →ₐ[R] D} (hπ : Function.Surjective π)
    {ε : D →ₐ[R] R} (hε : ∀ g, ε (π g) = constantCoeff g) :
    RingHom.ker ε = Ideal.span (Set.range fun j => π (X j)) := by
  refine le_antisymm (fun d hd => ?_) (Ideal.span_le.2 ?_)
  · obtain ⟨g, rfl⟩ := hπ d
    obtain ⟨a, ha⟩ := exists_matrix_eq_sum_mul_X (f := fun _ : Unit => g) fun _ => (hε g).symm.trans hd
    rw [ha (), map_sum]
    exact Ideal.sum_mem _ fun j _ => by
      rw [map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker, hε]

theorem map_det_mul_map_X {π : MvPowerSeries σ R →ₐ[R] D} {a : Matrix σ σ (MvPowerSeries σ R)}
    (ha : ∀ i, π (∑ j, a i j * X j) = 0) (j : σ) : π a.det * π (X j) = 0 := by
  rw [AlgHom.map_det]
  exact det_mul_eq_zero_of_sum_mul_eq_zero (x := fun j => π (X j)) (fun i => by simpa using ha i) j

theorem map_det_mem_annihilator_ker {π : MvPowerSeries σ R →ₐ[R] D} (hπ : Function.Surjective π)
    {ε : D →ₐ[R] R} (hε : ∀ g, ε (π g) = constantCoeff g) {a : Matrix σ σ (MvPowerSeries σ R)}
    (ha : ∀ i, π (∑ j, a i j * X j) = 0) : π a.det ∈ (RingHom.ker ε).annihilator := by
  rw [ker_eq_span_range_X hπ hε, AlgHom.map_det]
  exact det_mem_annihilator_span fun i => by simpa using ha i

theorem constantCoeff_det {a : Matrix σ σ (MvPowerSeries σ R)} {f : σ → MvPowerSeries σ R}
    (hf : ∀ i, f i = ∑ j, a i j * X j) :
    constantCoeff a.det = (Matrix.of fun i j => coeff (Finsupp.single j 1) (f i)).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [hf, coeff_single_sum_mul_X, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]

omit [Fintype σ] [DecidableEq σ] in

def quotientConstantCoeff {τ : Type*} (f : τ → MvPowerSeries σ R)
    (hf : ∀ i, constantCoeff (f i) = 0) :
    (MvPowerSeries σ R ⧸ Ideal.span (Set.range f)) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ { constantCoeff with commutes' := fun r => constantCoeff_C r }
    fun _ hg => (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hf i) :
      Ideal.span (Set.range f) ≤ germIdeal σ R) hg

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem quotientConstantCoeff_mk {τ : Type*} (f : τ → MvPowerSeries σ R)
    (hf : ∀ i, constantCoeff (f i) = 0) (g : MvPowerSeries σ R) :
    quotientConstantCoeff f hf (Ideal.Quotient.mk _ g) = constantCoeff g := rfl

omit [DecidableEq σ] in

theorem constantCoeff_eq_zero_of_eq_sum_mul_X {τ : Type*} {a : Matrix τ σ (MvPowerSeries σ R)}
    {f : τ → MvPowerSeries σ R} (hf : ∀ i, f i = ∑ j, a i j * X j) (i : τ) :
    constantCoeff (f i) = 0 := by
  simp [hf]

theorem cramer_quotient {a : Matrix σ σ (MvPowerSeries σ R)} {f : σ → MvPowerSeries σ R}
    (hf : ∀ i, f i = ∑ j, a i j * X j) :
    let ε := quotientConstantCoeff f (constantCoeff_eq_zero_of_eq_sum_mul_X hf)
    let Λ := Ideal.Quotient.mk (Ideal.span (Set.range f)) a.det
    (∀ j, Λ * Ideal.Quotient.mk _ (X j) = 0) ∧ Λ ∈ (RingHom.ker ε).annihilator ∧
      ε Λ = (a.map constantCoeff).det ∧
      ε Λ = (Matrix.of fun i j => coeff (Finsupp.single j 1) (f i)).det := by
  have ha (i) : Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)) (∑ j, a i j * X j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, hf i⟩)
  exact ⟨map_det_mul_map_X ha,
    map_det_mem_annihilator_ker (Ideal.Quotient.mkₐ_surjective R _) (fun _ => rfl) ha,
    RingHom.map_det (constantCoeff : MvPowerSeries σ R →+* R) a, constantCoeff_det hf⟩

end Cramer

universe u v w

theorem comodule_dual_invariants_integrals (R : Type u) [CommRing R] :
    (∀ (H : Type v) [Semiring H] [Bialgebra R H] [Module.Finite R H] [Module.Projective R H]
      (M : Type w) [AddCommGroup M] [Module R M],
      (∃ e : {ρ : M →ₗ[R] M ⊗[R] H // IsCoaction ρ} ≃ (CartierDual R H →ₐ[R] Module.End R M),
        ∀ ρ w m, e ρ w m = TensorProduct.rid R M (w.ofConv.lTensor M (ρ.1 m))) ∧
      (∀ (ρ : M →ₗ[R] M ⊗[R] H) (h : IsCoaction ρ) (m : M),
        (∀ w, h.dualAction w m = TensorProduct.rid R M (w.ofConv.lTensor M (ρ m))) ∧
        (ρ m = m ⊗ₜ 1 ↔ ∀ w : CartierDual R H, h.dualAction w m = w 1 • m) ∧
        ∀ Λ : CartierDual R H, (∀ w : CartierDual R H, w 1 = 0 → w * Λ = 0) →
          ρ (h.dualAction Λ m) = h.dualAction Λ m ⊗ₜ 1)) ∧
    (∀ (D : Type v) [CommRing D] [Algebra R D] (ε : D →ₐ[R] R),
      (∀ Λ, Λ ∈ (RingHom.ker ε).annihilator ↔ ∀ w, w * Λ = ε w • Λ) ∧
      (∀ (M : Type w) [AddCommGroup M] [Module R M] [Module D M] [IsScalarTower R D M],
        ∀ Λ ∈ (RingHom.ker ε).annihilator, ∀ (m : M) (w : D), w • Λ • m = ε w • Λ • m) ∧
      ∀ (K : Type w) [Field K] [Algebra R K] [Algebra.Etale K (K ⊗[R] D)],
        ∃ e : K ⊗[R] D, IsIdempotentElem e ∧ augmentationBaseChange K ε e = 1 ∧
          Function.Bijective
            ((augmentationBaseChange K ε).prod (Ideal.Quotient.mkₐ K (Ideal.span {e}))) ∧
          RingHom.ker (augmentationBaseChange K ε) = Ideal.span {1 - e} ∧
          (RingHom.ker (augmentationBaseChange K ε)).annihilator.restrictScalars K = K ∙ e ∧
          Module.finrank K
            ((RingHom.ker (augmentationBaseChange K ε)).annihilator.restrictScalars K) = 1 ∧
          ∀ Λ ∈ (RingHom.ker ε).annihilator, (1 : K) ⊗ₜ[R] Λ = algebraMap R K (ε Λ) • e) ∧
    (∀ (σ : Type v) [Fintype σ] [DecidableEq σ] (a : Matrix σ σ (MvPowerSeries σ R))
      (f : σ → MvPowerSeries σ R), (∀ i, f i = ∑ j, a i j * MvPowerSeries.X j) →
      ∃ ε : (MvPowerSeries σ R ⧸ Ideal.span (Set.range f)) →ₐ[R] R,
        (∀ g, ε (Ideal.Quotient.mk _ g) = MvPowerSeries.constantCoeff g) ∧
        (∀ j, Ideal.Quotient.mk (Ideal.span (Set.range f)) a.det *
          Ideal.Quotient.mk _ (MvPowerSeries.X j) = 0) ∧
        Ideal.Quotient.mk _ a.det ∈ (RingHom.ker ε).annihilator ∧
        ε (Ideal.Quotient.mk _ a.det) = (a.map MvPowerSeries.constantCoeff).det) := by
  refine ⟨fun H _ _ _ _ M _ _ => ⟨⟨coactionEquivDualAction R H M, fun ρ w m =>
      dualContraction_eq_rid ρ.1 w m⟩, fun ρ h m => ⟨fun w => dualContraction_eq_rid ρ w m,
      invariant_iff_dualContraction, fun Λ hΛ => h.invariant_dualContraction hΛ m⟩⟩,
    fun D _ _ ε => ⟨fun _ => mem_annihilator_ker_iff,
      fun M _ _ _ _ Λ hΛ => smul_smul_eq_of_mem_annihilator_ker hΛ, fun K _ _ _ => ?_⟩,
    fun σ _ _ a f hf => ⟨_, fun _ => rfl, (cramer_quotient hf).1, (cramer_quotient hf).2.1,
      (cramer_quotient hf).2.2.1⟩⟩
  obtain ⟨e, ⟨he, he1⟩, -⟩ := existsUnique_mem_annihilator_ker (augmentationBaseChange K ε)
  refine ⟨e, isIdempotentElem_of_mem_annihilator_ker he he1, he1,
    bijective_prod_quotient_of_mem_annihilator_ker he he1, ker_eq_span_one_sub he he1,
    annihilator_ker_restrictScalars_eq_span he he1, finrank_annihilator_ker _, fun Λ hΛ => ?_⟩
  simpa using eq_smul_of_mem_annihilator_ker he he1 (one_tmul_mem_annihilator_ker K hΛ)

section Examples

example : ¬ ∀ w : CartierDual ℤ (AddMonoidAlgebra ℤ (ZMod 2)),
    dualContraction (comul (R := ℤ)) w (AddMonoidAlgebra.single (1 : ZMod 2) (1 : ℤ)) =
      w 1 • AddMonoidAlgebra.single (1 : ZMod 2) (1 : ℤ) := fun h => by
  have h1 := h ((CartierDual.addMonoidAlgebraEquiv ℤ (ZMod 2)).symm (Pi.single 0 1))
  rw [dualContraction_apply, AddMonoidAlgebra.one_def] at h1
  simp [eq_comm] at h1

open MvPowerSeries in

example : ∃ ε : (MvPowerSeries Unit ℤ ⧸
      Ideal.span (Set.range fun _ : Unit => (2 + X ()) * (X () : MvPowerSeries Unit ℤ))) →ₐ[ℤ] ℤ,
    Ideal.Quotient.mk _ (2 + X ()) ∈ (RingHom.ker ε).annihilator ∧
      ε (Ideal.Quotient.mk _ (2 + X ())) = 2 := by
  have h := cramer_quotient (a := Matrix.of fun _ _ : Unit => (2 + X () : MvPowerSeries Unit ℤ))
    (f := fun _ : Unit => (2 + X ()) * X ()) (by simp)
  refine ⟨_, by simpa using h.2.1, ?_⟩
  simp [map_ofNat]

end Examples

end GlobalTheory
