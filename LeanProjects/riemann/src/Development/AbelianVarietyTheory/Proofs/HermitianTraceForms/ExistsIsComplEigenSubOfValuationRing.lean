import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub

open scoped TensorProduct NumberField
open Polynomial

namespace GlobalTheory

namespace EigenSplit

section Saturation

variable {O : Type*} [CommRing O] {R : Type*} [CommRing R]
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']

theorem isSaturatedSubmodule_eigenSub [IsDomain R] [Module.IsTorsionFree R N]
    (ρ : O →+* Module.End R N) (χ : O →+* R) : IsSaturatedSubmodule (eigenSub ρ χ) :=
  isSaturatedSubmodule_iff.2 fun c hc x hx => mem_eigenSub.2 fun a => by
    have h := mem_eigenSub.1 hx a
    rw [map_smul, smul_comm] at h
    exact smul_right_injective N hc h

theorem eigenSub_eq_iInf_ker (ρ : O →+* Module.End R N) (χ : O →+* R) {s : Set O}
    (hs : Submodule.span ℤ s = ⊤) :
    eigenSub ρ χ = ⨅ a : s, LinearMap.ker (ρ a - χ a • LinearMap.id) := by
  ext x
  simp only [mem_eigenSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine ⟨fun h a => h a, fun h a => ?_⟩
  have ha : a ∈ Submodule.span ℤ s := hs ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem a ha => exact h ⟨a, ha⟩
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb, add_smul]
  | smul n a _ ha => rw [map_zsmul, map_zsmul, LinearMap.smul_apply, ha, smul_assoc]

theorem IsEquivariant.symm {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {e : N ≃ₗ[R] N'} (he : IsEquivariant ρ ρ' (e : N →ₗ[R] N')) :
    IsEquivariant ρ' ρ (e.symm : N' →ₗ[R] N) := fun a y => by
  obtain ⟨x, rfl⟩ := e.surjective y
  have := he a x
  simp only [LinearEquiv.coe_coe] at this ⊢
  rw [← this, e.symm_apply_apply, e.symm_apply_apply]

theorem IsEquivariant.map_eigenSub {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {e : N ≃ₗ[R] N'} (he : IsEquivariant ρ ρ' (e : N →ₗ[R] N')) (χ : O →+* R) :
    (eigenSub ρ χ).map (e : N →ₗ[R] N') = eigenSub ρ' χ := by
  refine le_antisymm ?_ fun y hy => ⟨e.symm y, he.symm.map_mem hy, e.apply_symm_apply y⟩
  rintro _ ⟨x, hx, rfl⟩
  exact he.map_mem hx

def IsEquivariant.eigenLinearEquiv {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {e : N ≃ₗ[R] N'} (he : IsEquivariant ρ ρ' (e : N →ₗ[R] N')) (χ : O →+* R) :
    eigenSub ρ χ ≃ₗ[R] eigenSub ρ' χ :=
  e.ofSubmodules _ _ (he.map_eigenSub χ)

@[simp] theorem IsEquivariant.coe_eigenLinearEquiv {ρ : O →+* Module.End R N}
    {ρ' : O →+* Module.End R N'} {e : N ≃ₗ[R] N'} (he : IsEquivariant ρ ρ' (e : N →ₗ[R] N'))
    (χ : O →+* R) (x : eigenSub ρ χ) : (he.eigenLinearEquiv χ x : N') = e x := rfl

end Saturation

section FlatBaseChange

variable {O : Type*} [CommRing O] {R : Type*} [CommRing R]
  {N : Type*} [AddCommGroup N] [Module R N] {R' : Type*} [CommRing R'] [Algebra R R']
  {M : Type*} [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
  {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R' M} {f : N →ₗ[R] M}

theorem eigenSub_eq_comap (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hi : Function.Injective f)
    (χ : O →+* R) :
    eigenSub ρ χ = ((eigenSub ρ' ((algebraMap R R').comp χ)).restrictScalars R).comap f := by
  ext x
  refine ⟨fun hx => map_mem_eigenSub_algebraMap hf hx, fun hx => mem_eigenSub.2 fun a => hi ?_⟩
  rw [hf, map_smul, mem_eigenSub.1 hx a]
  simp

theorem isEquivariant_equiv (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange R' f) :
    IsEquivariant (baseChangeAction R' ρ) ρ' (hb.equiv : R' ⊗[R] N →ₗ[R'] M) := by
  intro a t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [hf]
  | add s t hs ht => simp only [map_add, hs, ht]

theorem charpoly_of_isBaseChange [Module.Free R N] [Module.Finite R N] [Module.Free R' M]
    [Module.Finite R' M] (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange R' f) (a : O) :
    (ρ' a).charpoly = (ρ a).charpoly.map (algebraMap R R') := by
  rw [← LinearMap.charpoly_baseChange, ← hb.equiv.charpoly_conj]
  congr 1
  ext y
  obtain ⟨t, rfl⟩ := hb.equiv.surjective y
  simpa using (isEquivariant_equiv hf hb a t).symm

variable [Module.Finite ℤ O] [Module.Flat R R']

variable (R' ρ) in

theorem eigenSub_baseChangeAction_of_flat (χ : O →+* R) :
    eigenSub (baseChangeAction R' ρ) ((algebraMap R R').comp χ)
      = (eigenSub ρ χ).baseChange R' := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := O)
  rw [eigenSub_eq_iInf_ker _ _ hs, eigenSub_eq_iInf_ker _ _ hs, baseChange_iInf]
  refine iInf_congr fun a => ?_
  rw [baseChange_ker]
  congr 1
  ext x
  simp [TensorProduct.tmul_sub]

theorem isBaseChange_eigenMapAlgebra_of_flat (hf : ∀ a x, f (ρ a x) = ρ' a (f x))
    (hb : IsBaseChange R' f) (χ : O →+* R) : IsBaseChange R' (eigenMapAlgebra hf χ) :=
  IsBaseChange.of_equiv (baseChangeEquiv R' (eigenSub ρ χ) ≪≫ₗ
    LinearEquiv.ofEq _ _ (eigenSub_baseChangeAction_of_flat R' ρ χ).symm ≪≫ₗ
    (isEquivariant_equiv hf hb).eigenLinearEquiv _) fun x => Subtype.ext (by simp)

theorem eigenSub_eq_span_of_flat (hf : ∀ a x, f (ρ a x) = ρ' a (f x))
    (hb : IsBaseChange R' f) (χ : O →+* R) :
    eigenSub ρ' ((algebraMap R R').comp χ) = Submodule.span R' (f '' eigenSub ρ χ) := by
  rw [← (isEquivariant_equiv hf hb).map_eigenSub, eigenSub_baseChangeAction_of_flat,
    Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
  simp

theorem finrank_eigenSub_of_flat [NoZeroDivisors R'] [FaithfulSMul R R']
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange R' f) (χ : O →+* R) :
    Module.finrank R' (eigenSub ρ' ((algebraMap R R').comp χ))
      = Module.finrank R (eigenSub ρ χ) :=
  (isBaseChange_eigenMapAlgebra_of_flat hf hb χ).finrank_eq

end FlatBaseChange

section Tower

variable (A : Type*) [CommRing A] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
  [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
  (N : Type*) [AddCommGroup N] [Module A N]

noncomputable def extendTensor : S ⊗[A] N →ₗ[S] T ⊗[A] N :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap S T) LinearMap.id

variable {A S N} in
@[simp] theorem extendTensor_tmul (s : S) (x : N) :
    extendTensor A S T N (s ⊗ₜ x) = algebraMap S T s ⊗ₜ x := rfl

theorem isBaseChange_extendTensor : IsBaseChange T (extendTensor A S T N) :=
  isBaseChange_tensorProduct_map T (IsBaseChange.linearMap S T)

variable {A N} in
theorem extendTensor_equivariant {O : Type*} [CommRing O] (ρ : O →+* Module.End A N) (a : O)
    (x : S ⊗[A] N) : extendTensor A S T N (baseChangeAction S ρ a x)
      = baseChangeAction T ρ a (extendTensor A S T N x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp
  | add s t hs ht => simp only [map_add, hs, ht]

theorem extendTensor_injective [Module.Flat A N] [FaithfulSMul S T] :
    Function.Injective (extendTensor A S T N) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := N)
    (IsScalarTower.toAlgHom A S T).toLinearMap (FaithfulSMul.algebraMap_injective S T)

end Tower

section Determinant

variable {O : Type*} [CommRing O] [Module.Finite ℤ O] {A : Type*} [CommRing A] [IsDomain A]
  {ι : Type*} [Fintype ι] {σ : ι → O →+* A}
  {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] {ρ : O →+* Module.End A N}

omit [Module.Finite ℤ O] in

theorem isSplitting_comp_of_injective
    (h : IsSplitting fun i => (algebraMap A (FractionRing A)).comp (σ i))
    {L : Type*} [Field L] {g : A →+* L} (hg : Function.Injective g) :
    IsSplitting fun i => g.comp (σ i) := by
  convert h.map (IsFractionRing.lift (K := FractionRing A) hg) using 2 with i
  ext a
  simp

omit [Module.Finite ℤ O] in

theorem isSplitting_fractionRing_of_injective
    (h : IsSplitting fun i => (algebraMap A (FractionRing A)).comp (σ i))
    {B : Type*} [CommRing B] [IsDomain B] {g : A →+* B} (hg : Function.Injective g) :
    IsSplitting fun i => (algebraMap B (FractionRing B)).comp (g.comp (σ i)) :=
  isSplitting_comp_of_injective h (g := (algebraMap B (FractionRing B)).comp g)
    ((IsFractionRing.injective B (FractionRing B)).comp hg)

variable (h : IsSplitting fun i => (algebraMap A (FractionRing A)).comp (σ i))
include h

variable (ρ) in

theorem charpoly_eq_prod_of_isDomain [Module.Free A N] (a : O) :
    (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ Module.finrank A (eigenSub ρ (σ i)) := by
  apply Polynomial.map_injective _ (IsFractionRing.injective A (FractionRing A))
  have hf := mk_equivariant (FractionRing A) ρ
  have hb := TensorProduct.isBaseChange A N (FractionRing A)
  rw [← charpoly_of_isBaseChange hf hb, charpoly_eq_prod_of_isLocalRing h]
  simp [Polynomial.map_prod, finrank_eigenSub_of_flat hf hb]

variable [Module.Flat A N] {S : Type*} [CommRing S] [Algebra A S]
  {M : Type*} [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
  {ρ' : O →+* Module.End S M} {f : N →ₗ[A] M}

private theorem charpoly_eq_prod_local [IsLocalRing S] [Module.Free S M] [Module.Finite S M]
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange S f) (a : O) :
    (ρ' a).charpoly = ∏ i, (X - C (algebraMap A S (σ i a)))
      ^ Module.finrank A (eigenSub ρ (σ i)) := by
  let p : Ideal A := (IsLocalRing.maximalIdeal S).comap (algebraMap A S)
  let B := Localization.AtPrime p
  let g : B →+* S := IsLocalization.lift (M := p.primeCompl) (g := algebraMap A S) fun y =>
    (IsLocalRing.notMem_maximalIdeal).1 y.2
  let : Algebra B S := g.toAlgebra
  have : IsScalarTower A B S := .of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm
  let : Module B M := Module.compHom M g
  have : IsScalarTower B S M := ⟨fun x y z => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : IsScalarTower A B M := IsScalarTower.to₁₂₄ _ _ S _
  have : Module.Free B (B ⊗[A] N) := Module.free_of_flat_of_isLocalRing
  have hinj : Function.Injective (algebraMap A B) :=
    IsLocalization.injective B p.primeCompl_le_nonZeroDivisors
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hB := TensorProduct.isBaseChange A N B
  have hb' : IsBaseChange S (hB.lift f) := hB.of_comp (by rwa [hB.lift_comp])
  have hf' : ∀ a x, hB.lift f (baseChangeAction B ρ a x) = ρ' a (hB.lift f x) := by
    intro a x
    induction x using hB.inductionOn with
    | zero => simp
    | tmul x => rw [← mk_equivariant, hB.lift_eq, hB.lift_eq, hf]
    | smul s x hx =>
      rw [map_smul, map_smul, map_smul, hx, ← algebraMap_smul S s, ← algebraMap_smul S s, map_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [charpoly_of_isBaseChange hf' hb',
    charpoly_eq_prod_of_isDomain _ (isSplitting_fractionRing_of_injective h hinj)]
  simp [Polynomial.map_prod, finrank_eigenSub_of_flat (mk_equivariant B ρ) hB,
    ← IsScalarTower.algebraMap_apply]

theorem charpoly_eq_prod_of_isBaseChange [Module.Free S M] [Module.Finite S M]
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange S f) (a : O) :
    (ρ' a).charpoly = ∏ i, (X - C (algebraMap A S (σ i a)))
      ^ Module.finrank A (eigenSub ρ (σ i)) := by
  ext n
  refine Module.eq_of_localization_maximal (R := S) (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap S (Localization.AtPrime P)) _ _ fun m hm => ?_
  let T := Localization.AtPrime m
  have hT := TensorProduct.isBaseChange S M T
  have h1 := charpoly_eq_prod_local h (ρ := ρ) (ρ' := baseChangeAction T ρ')
    (fun a x => by simp [hf]) (hb.comp hT) a
  rw [charpoly_of_isBaseChange (mk_equivariant T ρ') hT] at h1
  have h2 : (∏ i, (X - C (algebraMap A S (σ i a))) ^ Module.finrank A (eigenSub ρ (σ i))).map
      (algebraMap S T) = ∏ i, (X - C (algebraMap A T (σ i a)))
      ^ Module.finrank A (eigenSub ρ (σ i)) := by
    simp [Polynomial.map_prod, ← IsScalarTower.algebraMap_apply]
  have := congrArg (fun q => Polynomial.coeff q n) (h1.trans h2.symm)
  simp only [Polynomial.coeff_map] at this
  exact this

theorem finrank_eigenSub_of_isLocalRing [IsLocalRing S]
    (hS : IsSplitting fun i => (algebraMap A S).comp (σ i))
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange S f) (i : ι) :
    Module.finrank S (eigenSub ρ' ((algebraMap A S).comp (σ i)))
      = Module.finrank A (eigenSub ρ (σ i)) := by
  have : Module.Finite S M := Module.Finite.equiv hb.equiv
  have : Module.Flat S M := Module.Flat.of_linearEquiv hb.equiv.symm
  have : Module.Free S M := Module.free_of_flat_of_isLocalRing
  exact (charpoly_eq_iff_finrank_eq hS ρ' fun i => Module.finrank A (eigenSub ρ (σ i))).1
    (charpoly_eq_prod_of_isBaseChange h hf hb) i

theorem rankAtStalk_eigenSub (hS : IsSplitting fun i => (algebraMap A S).comp (σ i))
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange S f) (i : ι) (p : PrimeSpectrum S) :
    Module.rankAtStalk (eigenSub ρ' ((algebraMap A S).comp (σ i))) p
      = Module.finrank A (eigenSub ρ (σ i)) := by
  let T := Localization.AtPrime p.asIdeal
  have hT := TensorProduct.isBaseChange S M T
  have e : ∀ i, (algebraMap S T).comp ((algebraMap A S).comp (σ i))
      = (algebraMap A T).comp (σ i) := fun i => by
    rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have hs := hS.map (algebraMap S T)
  simp only [e] at hs
  rw [Module.rankAtStalk_eq_finrank_tensorProduct, (eigenBaseChangeEquiv T ρ' hS i).finrank_eq, e]
  exact finrank_eigenSub_of_isLocalRing h hs (fun a x => by simp [hf]) (hb.comp hT) i

theorem finrank_eigenSub_of_isDomain [IsDomain S]
    (hS : IsSplitting fun i => (algebraMap S (FractionRing S)).comp ((algebraMap A S).comp (σ i)))
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange S f) (i : ι) :
    Module.finrank S (eigenSub ρ' ((algebraMap A S).comp (σ i)))
      = Module.finrank A (eigenSub ρ (σ i)) := by
  let T := FractionRing S
  have hT := TensorProduct.isBaseChange S M T
  have e : ∀ i, (algebraMap S T).comp ((algebraMap A S).comp (σ i))
      = (algebraMap A T).comp (σ i) := fun i => by
    rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have hs : IsSplitting fun i => (algebraMap A T).comp (σ i) := by simpa only [← e] using hS
  rw [← finrank_eigenSub_of_flat (mk_equivariant T ρ') hT, e]
  exact finrank_eigenSub_of_isLocalRing h hs (fun a x => by simp [hf]) (hb.comp hT) i

end Determinant

section Factor

variable {O : Type*} [CommRing O] [Module.Finite ℤ O] {A : Type*} [CommRing A]
  {ι : Type*} [Finite ι] {σ : ι → O →+* A}
  {N : Type*} [AddCommGroup N] [Module A N] {ρ : O →+* Module.End A N}
  {S : Type*} [CommRing S] [Algebra A S]
  {M : Type*} [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
  {ρ' : O →+* Module.End S M} {f : N →ₗ[A] M}

omit [Module.Finite ℤ O] in
private theorem eigenSub_eq_span_of_isBaseChange {hf : ∀ a x, f (ρ a x) = ρ' a (f x)}
    {χ : O →+* A} (hb : IsBaseChange S (eigenMapAlgebra hf χ)) :
    eigenSub ρ' ((algebraMap A S).comp χ) = Submodule.span S (f '' eigenSub ρ χ) := by
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · change ((⟨y, hy⟩ : eigenSub ρ' ((algebraMap A S).comp χ)) : M) ∈ _
    refine hb.inductionOn ⟨y, hy⟩
      (fun z => (z : M) ∈ Submodule.span S (f '' eigenSub ρ χ)) (Submodule.zero_mem _)
      (fun x => Submodule.subset_span ⟨x, x.2, rfl⟩) (fun s _ hz => Submodule.smul_mem _ s hz)
      fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂
  · rintro _ ⟨x, hx, rfl⟩
    exact map_mem_eigenSub_algebraMap hf hx

theorem eigenSub_eq_span_of_factor (B : Type*) [CommRing B] [Algebra A B] [Module.Flat A B]
    [Algebra B S] [IsScalarTower A B S] (hB : IsSplitting fun i => (algebraMap A B).comp (σ i))
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange S f) (i : ι) :
    eigenSub ρ' ((algebraMap A S).comp (σ i)) = Submodule.span S (f '' eigenSub ρ (σ i)) := by
  let : Module B M := Module.compHom M (algebraMap B S)
  have : IsScalarTower B S M := ⟨fun x y z => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : IsScalarTower A B M := IsScalarTower.to₁₂₄ _ _ S _
  have hN := TensorProduct.isBaseChange A N B
  have hb' : IsBaseChange S (hN.lift f) := hN.of_comp (by rwa [hN.lift_comp])
  have hf' : ∀ a x, hN.lift f (baseChangeAction B ρ a x) = ρ' a (hN.lift f x) := by
    intro a x
    induction x using hN.inductionOn with
    | zero => simp
    | tmul x => rw [← mk_equivariant, hN.lift_eq, hN.lift_eq, hf]
    | smul s x hx =>
      rw [map_smul, map_smul, map_smul, hx, ← algebraMap_smul S s, ← algebraMap_smul S s, map_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h1 := eigenSub_eq_span_of_isBaseChange (isBaseChange_eigenMapAlgebra hB hf' hb' i)
  rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq,
    eigenSub_eq_span_of_flat (mk_equivariant B ρ) hN, ← Submodule.map_coe, Submodule.map_span,
    Submodule.span_span_of_tower, Set.image_image] at h1
  simpa only [hN.lift_eq] using h1

end Factor

section Valuation

variable {O : Type*} [CommRing O] {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
  {M : Type*} [AddCommGroup M] [Module V M]

variable (V) in

theorem flat_of_valuationRing (V' : Type*) [CommRing V'] [IsDomain V'] [Algebra V V']
    [FaithfulSMul V V'] : Module.Flat V V' :=
  Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1
      (Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective V V')))

variable [Module.Finite V M] [Module.IsTorsionFree V M] (ρ : O →+* Module.End V M) (χ : O →+* V)

theorem finite_eigenSub_of_valuationRing : Module.Finite V (eigenSub ρ χ) :=
  (isSaturatedSubmodule_eigenSub ρ χ).finite_of_valuationRing

theorem free_eigenSub_of_valuationRing : Module.Free V (eigenSub ρ χ) :=
  (isSaturatedSubmodule_eigenSub ρ χ).free_of_valuationRing

theorem exists_isCompl_eigenSub_of_valuationRing : ∃ Q : Submodule V M, IsCompl (eigenSub ρ χ) Q :=
  (isSaturatedSubmodule_eigenSub ρ χ).exists_isCompl_of_valuationRing

end Valuation

section Frames

variable {R : Type*} [CommRing R] {K : Type*} [CommRing K] [Algebra R K]
  {P : Type*} [AddCommGroup P] [Module R P]
  {W : Type*} [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]
  {ι : Type*} [Fintype ι] (b b' : Module.Basis ι R P) (j : P →ₗ[R] W)

theorem eq_map_toMatrix_of_eq_sum (hli : LinearIndependent K fun i => j (b' i))
    {g : Matrix ι ι K} (hg : ∀ k, j (b k) = ∑ i, g i k • j (b' i)) :
    g = (b'.toMatrix b).map (algebraMap R K) := by
  ext i k
  refine Fintype.linearIndependent_iffₛ.1 hli (fun i => g i k)
    (fun i => algebraMap R K (b'.toMatrix b i k)) ?_ i
  rw [← hg, ← b'.sum_toMatrix_smul_self b k, map_sum]
  simp

variable [LinearOrder ι]

theorem isUpperTriangular_toMatrix_of_mem_span [FaithfulSMul R K]
    (hli : LinearIndependent K fun i => j (b' i))
    (h : ∀ k, j (b k) ∈ Submodule.span K ((fun i => j (b' i)) '' Set.Iic k)) :
    (b'.toMatrix b).IsUpperTriangular := by
  choose l hl hl' using fun k => (Finsupp.mem_span_image_iff_linearCombination K).1 (h k)
  have hg := eq_map_toMatrix_of_eq_sum b b' j hli (g := Matrix.of fun i k => l k i) fun k => by
    rw [← hl' k, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    rfl
  intro i k hik
  apply FaithfulSMul.algebraMap_injective R K
  have h1 : l k i = algebraMap R K (b'.toMatrix b i k) := congrFun (congrFun hg i) k
  rw [← h1, map_zero]
  exact (Finsupp.mem_supported' K _).1 (hl k) i (not_le.2 hik)

theorem isUnit_diag_of_isUpperTriangular {g : Matrix ι ι R} (hg : g.IsUpperTriangular)
    (hu : IsUnit g.det) (i : ι) : IsUnit (g i i) := by
  rw [Matrix.det_of_isUpperTriangular hg] at hu
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => g i i) (Finset.mem_univ i)) hu

theorem exists_triangular_of_mem_span [FaithfulSMul R K]
    (hli : LinearIndependent K fun i => j (b' i))
    (h : ∀ k, j (b k) ∈ Submodule.span K ((fun i => j (b' i)) '' Set.Iic k)) :
    ∃ g : GL ι R, (g : Matrix ι ι R).IsUpperTriangular ∧ (∀ i, IsUnit (g i i)) ∧
      (∀ k, b k = ∑ i, g i k • b' i) ∧
      ∀ g' : Matrix ι ι K, (∀ k, j (b k) = ∑ i, g' i k • j (b' i)) →
        g' = (g : Matrix ι ι R).map (algebraMap R K) := by
  have ht := isUpperTriangular_toMatrix_of_mem_span b b' j hli h
  exact ⟨⟨b'.toMatrix b, b.toMatrix b', b'.toMatrix_mul_toMatrix_flip b,
    b.toMatrix_mul_toMatrix_flip b'⟩, ht, isUnit_diag_of_isUpperTriangular ht (b'.isUnit_det b),
    fun k => (b'.sum_toMatrix_smul_self b k).symm,
    fun _ hg => eq_map_toMatrix_of_eq_sum b b' j hli hg⟩

omit [Fintype ι] [LinearOrder ι] in

theorem linearIndependent_of_isBaseChange [Module.Flat R K] {f : P →ₗ[R] W}
    (hb : IsBaseChange K f) {v : ι → P} (hv : LinearIndependent R v) :
    LinearIndependent K fun i => f (v i) := by
  have := (Module.Flat.linearIndependent_one_tmul (S := K) hv).map' hb.equiv.toLinearMap
    hb.equiv.ker
  simpa [Function.comp_def] using this

variable {O : Type*} [CommRing O] {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] {ρ : O →+* Module.End R M} {ρ' : O →+* Module.End R M'}

theorem IsEquivariant.exists_triangular [FaithfulSMul R K] [Module.Flat R K] {e : M ≃ₗ[R] M'}
    (he : IsEquivariant ρ ρ' (e : M →ₗ[R] M')) {χ : O →+* R}
    (c : Module.Basis ι R (eigenSub ρ χ)) (c' : Module.Basis ι R (eigenSub ρ' χ))
    {F : ι → Submodule K (K ⊗[R] M)} {F' : ι → Submodule K (K ⊗[R] M')}
    (hc : ∀ k, Submodule.span K ((fun i => (1 : K) ⊗ₜ[R] (c i : M)) '' Set.Iic k) = F k)
    (hc' : ∀ k, Submodule.span K ((fun i => (1 : K) ⊗ₜ[R] (c' i : M')) '' Set.Iic k) = F' k)
    (hF : ∀ k, (F k).map ((e : M →ₗ[R] M').baseChange K) = F' k) :
    ∃ g : GL ι R, (g : Matrix ι ι R).IsUpperTriangular ∧ (∀ i, IsUnit (g i i)) ∧
      (∀ k, e (c k) = ∑ i, g i k • (c' i : M')) ∧
      ∀ g' : Matrix ι ι K,
        (∀ k, (1 : K) ⊗ₜ[R] e (c k) = ∑ i, g' i k • (1 : K) ⊗ₜ[R] (c' i : M')) →
        g' = (g : Matrix ι ι R).map (algebraMap R K) := by
  have hli := linearIndependent_of_isBaseChange (TensorProduct.isBaseChange R M' K)
    (c'.linearIndependent.map' (eigenSub ρ' χ).subtype (Submodule.ker_subtype _))
  obtain ⟨g, h1, h2, h3, h4⟩ := exists_triangular_of_mem_span (K := K)
    (c.map (he.eigenLinearEquiv χ)) c' (TensorProduct.mk R K M' 1 ∘ₗ (eigenSub ρ' χ).subtype)
    hli fun k => by
      have : (1 : K) ⊗ₜ[R] e (c k) ∈ F' k := by
        rw [← hF, ← hc]
        exact ⟨_, Submodule.subset_span ⟨k, le_rfl, rfl⟩, rfl⟩
      rw [← hc'] at this
      exact this
  refine ⟨g, h1, h2, fun k => ?_, h4⟩
  simpa using congrArg Subtype.val (h3 k)

end Frames

section Integers

variable {E : Type*} [Field E] [NumberField E] {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
  {ι : Type*} [Fintype ι] {σ : ι → 𝓞 E →+* A}

omit [CharZero A] in

theorem flat_int_iff_charZero : Module.Flat ℤ A ↔ CharZero A := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot, Module.isTorsionFree_iff_algebraMap_injective]
  exact ⟨fun h => charZero_of_injective_algebraMap h, fun _ => RingHom.injective_int _⟩

omit [IsDomain A] [CharZero A] in
theorem isUnit_discr_of_charZero (K : Type*) [Field K] [CharZero K] :
    IsUnit (NumberField.discr E : K) := by
  simpa using NumberField.discr_ne_zero E

theorem conjugateHom_injective {L : Type*} [Field L] [Algebra (𝓞 L) A] {φ : ι → E →+* L}
    (hφ : Function.Injective φ) (hc : Fintype.card ι = Module.finrank ℚ E) :
    Function.Injective fun i => conjugateHom L A (φ i) := by
  classical
  obtain ⟨b⟩ := nonempty_basis hc
  have := (isSplitting_of_isUnit_discr b (det_sq_eq_discr_map (det_sq_conjugateHom hφ b)
    (algebraMap A (FractionRing A))) (isUnit_discr_of_charZero _)).injective
  exact fun i j hij => this (congrArg (algebraMap A (FractionRing A)).comp hij)

variable (hσ : Function.Injective σ) (hc : Fintype.card ι = Module.finrank ℚ E)
include hσ hc

theorem isSplitting_fractionRing :
    IsSplitting fun i => (algebraMap A (FractionRing A)).comp (σ i) :=
  isSplitting_of_isDomain hσ hc _ (isUnit_discr_of_charZero _)

variable {N : Type*} [AddCommGroup N] [Module A N] {ρ : 𝓞 E →+* Module.End A N}
  {S : Type*} [CommRing S] [Algebra A S]
  {M : Type*} [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
  {ρ' : 𝓞 E →+* Module.End S M} {f : N →ₗ[A] M}

theorem eigenSub_eq_span_of_isUnit_discr (hu : IsUnit (NumberField.discr E : S))
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange S f) (i : ι) :
    eigenSub ρ' ((algebraMap A S).comp (σ i)) = Submodule.span S (f '' eigenSub ρ (σ i)) := by
  have hu' : IsUnit (algebraMap A S (NumberField.discr E : A)) := by rwa [map_intCast]
  let B := Localization.Away (NumberField.discr E : A)
  let : Algebra B S := (IsLocalization.Away.lift (NumberField.discr E : A) hu').toAlgebra
  have : IsScalarTower A B S := .of_algebraMap_eq' (IsLocalization.Away.lift_comp _ hu').symm
  refine eigenSub_eq_span_of_factor B (isSplitting_of_isDomain hσ hc _ ?_) hf hb i
  simpa using IsLocalization.Away.algebraMap_isUnit (S := B) (NumberField.discr E : A)

theorem eigenSub_eq_saturation [IsDomain S] [CharZero S] [Module.IsTorsionFree S M]
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange S f) (i : ι) :
    eigenSub ρ' ((algebraMap A S).comp (σ i))
      = saturation (Submodule.span S (f '' eigenSub ρ (σ i))) := by
  let K := FractionRing S
  have hK := TensorProduct.isBaseChange S M K
  have hl := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).2 hK
  have hi : Function.Injective (TensorProduct.mk S K M 1) :=
    (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors S) _).2 fun c =>
      smul_right_injective M (nonZeroDivisors.coe_ne_zero c)
  have h1 := eigenSub_eq_span_of_isUnit_discr hσ hc (ρ := ρ) (ρ' := baseChangeAction K ρ')
    (isUnit_discr_of_charZero K) (fun a x => by simp [hf]) (hb.comp hK) i
  rw [saturation_eq_comap_localized' K (TensorProduct.mk S K M 1), Submodule.localized'_eq_span,
    ← Submodule.map_coe, Submodule.map_span, Submodule.span_span_of_tower, Set.image_image,
    eigenSub_eq_comap (mk_equivariant K ρ') hi,
    ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, h1]
  rfl

variable [Module.Finite A N] [Module.Flat A N]

theorem finrank_eigenSub_of_charZero [IsDomain S] [CharZero S]
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange S f) (i : ι) :
    Module.finrank S (eigenSub ρ' ((algebraMap A S).comp (σ i)))
      = Module.finrank A (eigenSub ρ (σ i)) :=
  finrank_eigenSub_of_isDomain (isSplitting_fractionRing hσ hc)
    (isSplitting_of_isDomain hσ hc ((algebraMap S (FractionRing S)).comp (algebraMap A S))
      (isUnit_discr_of_charZero _)) hf hb i

theorem eq_finrank_of_charpoly [Module.Free S M] [Module.Finite S M]
    (hd : ¬ IsNilpotent (NumberField.discr E : S))
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange S f) (r : ι → ℕ)
    (hr : ∀ a, (ρ' a).charpoly = ∏ i, (X - C (algebraMap A S (σ i a))) ^ r i) (i : ι) :
    r i = Module.finrank A (eigenSub ρ (σ i)) := by
  let T := Localization.Away (NumberField.discr E : S)
  have : Nontrivial T := not_subsingleton_iff_nontrivial.1 fun h =>
    hd ((IsLocalization.subsingleton_iff (M := Submonoid.powers (NumberField.discr E : S))).1 h)
  have hs := isSplitting_of_isDomain hσ hc ((algebraMap S T).comp (algebraMap A S))
    (by simpa using IsLocalization.Away.algebraMap_isUnit (S := T) (NumberField.discr E : S))
  refine congrFun (hs.exponents_eq r (fun i => Module.finrank A (eigenSub ρ (σ i))) fun a => ?_) i
  have := congrArg (Polynomial.map (algebraMap S T)) ((hr a).symm.trans
    (charpoly_eq_prod_of_isBaseChange (isSplitting_fractionRing hσ hc) hf hb a))
  simpa [Polynomial.map_prod] using this

end Integers

end EigenSplit

universe u v

open EigenSplit in

theorem eigenBundle_of_injective {E : Type*} [Field E] [NumberField E]
    {A : Type u} [CommRing A] [IsDomain A] [CharZero A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {σ : ι → 𝓞 E →+* A} (hσ : Function.Injective σ) (hc : Fintype.card ι = Module.finrank ℚ E)
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Projective A N]
    (ρ : 𝓞 E →+* Module.End A N) :
    ∃ r : ι → ℕ,
      (∀ i, Module.rank A (eigenSub ρ (σ i)) = r i) ∧
      (Nontrivial (Localization.Away (NumberField.discr E : A)) ∧
        IsUnit (NumberField.discr E : Localization.Away (NumberField.discr E : A))) ∧
      (∀ (S : Type u) [CommRing S] [Algebra A S], IsUnit (NumberField.discr E : S) →
        DirectSum.IsInternal
          (fun i => eigenSub (baseChangeAction S ρ) ((algebraMap A S).comp (σ i))) ∧
        ∀ i, eigenSub (baseChangeAction S ρ) ((algebraMap A S).comp (σ i))
            = (eigenSub ρ (σ i)).baseChange S ∧
          Module.Finite S (eigenSub (baseChangeAction S ρ) ((algebraMap A S).comp (σ i))) ∧
          Module.Projective S
            (eigenSub (baseChangeAction S ρ) ((algebraMap A S).comp (σ i))) ∧
          ∀ p : PrimeSpectrum S, Module.rankAtStalk
            (eigenSub (baseChangeAction S ρ) ((algebraMap A S).comp (σ i))) p = r i) ∧
      (∀ (S : Type u) [CommRing S] [Algebra A S] [Module.Free S (S ⊗[A] N)],
        (∀ a, (baseChangeAction S ρ a).charpoly
          = ∏ i, (X - C (algebraMap A S (σ i a))) ^ r i) ∧
        (¬ IsNilpotent (NumberField.discr E : S) → ∀ r' : ι → ℕ,
          (∀ a, (baseChangeAction S ρ a).charpoly
            = ∏ i, (X - C (algebraMap A S (σ i a))) ^ r' i) → r' = r)) ∧
      (∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [CharZero V] [Algebra A V]
        (i : ι) (P : Submodule V (V ⊗[A] N)),
        P = eigenSub (baseChangeAction V ρ) ((algebraMap A V).comp (σ i)) →
        IsSaturatedSubmodule P ∧ P = saturation ((eigenSub ρ (σ i)).baseChange V) ∧
        Module.Finite V P ∧ Module.Free V P ∧ Module.finrank V P = r i ∧
        (∃ Q, IsCompl P Q) ∧
        (∀ (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K] [Algebra A K]
          [IsScalarTower A V K] (W : Submodule K (K ⊗[A] N)),
          W = eigenSub (baseChangeAction K ρ) ((algebraMap A K).comp (σ i)) →
          Function.Injective (extendTensor A V K N) ∧ IsBaseChange K (extendTensor A V K N) ∧
          P = (W.restrictScalars V).comap (extendTensor A V K N) ∧
          Submodule.span K (extendTensor A V K N '' P) = W ∧ Module.finrank K W = r i) ∧
        ∀ (V' : Type u) [CommRing V'] [IsDomain V'] [ValuationRing V'] [Algebra V V']
          [FaithfulSMul V V'] [Algebra A V'] [IsScalarTower A V V'] (P' : Submodule V' (V' ⊗[A] N)),
          P' = eigenSub (baseChangeAction V' ρ) ((algebraMap A V').comp (σ i)) →
          Submodule.span V' (extendTensor A V V' N '' P) = P' ∧
          ∃ e : V' ⊗[V] P ≃ₗ[V'] P', ∀ x : P,
            (e (1 ⊗ₜ x) : V' ⊗[A] N) = extendTensor A V V' N x) ∧
      ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
        (M M' : Type v) [AddCommGroup M] [Module V M] [AddCommGroup M'] [Module V M']
        (τ : 𝓞 E →+* Module.End V M) (τ' : 𝓞 E →+* Module.End V M') (e : M ≃ₗ[V] M'),
        (∀ a x, e (τ a x) = τ' a (e x)) → ∀ χ : 𝓞 E →+* V,
        (eigenSub τ χ).map (e : M →ₗ[V] M') = eigenSub τ' χ ∧
        ∀ (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K] (n : ℕ)
          (c : Module.Basis (Fin n) V (eigenSub τ χ)) (c' : Module.Basis (Fin n) V (eigenSub τ' χ))
          (F : Fin n → Submodule K (K ⊗[V] M)) (F' : Fin n → Submodule K (K ⊗[V] M')),
          (∀ k, Submodule.span K ((fun j => (1 : K) ⊗ₜ[V] (c j : M)) '' Set.Iic k) = F k) →
          (∀ k, Submodule.span K ((fun j => (1 : K) ⊗ₜ[V] (c' j : M')) '' Set.Iic k) = F' k) →
          (∀ k, (F k).map ((e : M →ₗ[V] M').baseChange K) = F' k) →
          ∃ g : GL (Fin n) V, (g : Matrix (Fin n) (Fin n) V).IsUpperTriangular ∧
            (∀ j, IsUnit (g j j)) ∧ (∀ k, e (c k) = ∑ j, g j k • (c' j : M')) ∧
            ∀ g' : Matrix (Fin n) (Fin n) K,
              (∀ k, (1 : K) ⊗ₜ[V] e (c k) = ∑ j, g' j k • (1 : K) ⊗ₜ[V] (c' j : M')) →
              g' = (g : Matrix (Fin n) (Fin n) V).map (algebraMap V K) := by
  have h := isSplitting_fractionRing hσ hc
  refine ⟨fun i => Module.finrank A (eigenSub ρ (σ i)), fun i => ?_, ⟨?_, ?_⟩,
    fun S _ _ hu => ?_, fun S _ _ _ => ⟨?_, fun hd r' hr => ?_⟩, ?_, ?_⟩
  · exact (Cardinal.cast_toNat_of_lt_aleph0
      ((Submodule.rank_le _).trans_lt (Module.rank_lt_aleph0 A N))).symm
  · have hd : (NumberField.discr E : A) ≠ 0 := by simpa using NumberField.discr_ne_zero E
    exact (IsLocalization.injective (Localization.Away (NumberField.discr E : A))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hd)).nontrivial
  · simpa using IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (NumberField.discr E : A)) (NumberField.discr E : A)
  · have hS := isSplitting_of_isDomain hσ hc (algebraMap A S) hu
    have hb := TensorProduct.isBaseChange A N S
    refine ⟨isInternal_eigenSub hS _, fun i => ⟨?_, finite_eigenSub hS _ i,
      projective_eigenSub hS _ i, rankAtStalk_eigenSub h hS (mk_equivariant S ρ) hb i⟩⟩
    rw [eigenSub_eq_span_of_isUnit_discr hσ hc hu (mk_equivariant S ρ) hb,
      Submodule.baseChange_eq_span, Submodule.map_coe]
  · exact charpoly_eq_prod_of_isBaseChange h (mk_equivariant S ρ)
      (TensorProduct.isBaseChange A N S)
  · exact funext (eq_finrank_of_charpoly hσ hc hd (mk_equivariant S ρ)
      (TensorProduct.isBaseChange A N S) r' hr)
  · rintro V _ _ _ _ _ i _ rfl
    have hb := TensorProduct.isBaseChange A N V
    have : Module.Free V (V ⊗[A] N) := Module.free_of_flat_of_isLocalRing
    refine ⟨isSaturatedSubmodule_eigenSub _ _, ?_, finite_eigenSub_of_valuationRing _ _,
      free_eigenSub_of_valuationRing _ _,
      finrank_eigenSub_of_charZero hσ hc (mk_equivariant V ρ) hb i,
      exists_isCompl_eigenSub_of_valuationRing _ _, ?_, ?_⟩
    · rw [eigenSub_eq_saturation hσ hc (mk_equivariant V ρ) hb,
        Submodule.baseChange_eq_span, Submodule.map_coe]
    · rintro K _ _ _ _ _ _ rfl
      have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
      have := flat_of_valuationRing V K
      have e : (algebraMap A K).comp (σ i)
          = (algebraMap V K).comp ((algebraMap A V).comp (σ i)) := by
        rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
      refine ⟨extendTensor_injective A V K N, isBaseChange_extendTensor A V K N, ?_, ?_,
        finrank_eigenSub_of_charZero hσ hc (mk_equivariant K ρ)
          (TensorProduct.isBaseChange A N K) i⟩
      · rw [e]
        exact eigenSub_eq_comap (extendTensor_equivariant V K ρ) (extendTensor_injective A V K N) _
      · rw [e]
        exact (eigenSub_eq_span_of_flat (extendTensor_equivariant V K ρ)
          (isBaseChange_extendTensor A V K N) _).symm
    · rintro V' _ _ _ _ _ _ _ P' hP'
      have := flat_of_valuationRing V V'
      rw [IsScalarTower.algebraMap_eq A V V', RingHom.comp_assoc] at hP'
      subst hP'
      exact ⟨(eigenSub_eq_span_of_flat (extendTensor_equivariant V V' ρ)
          (isBaseChange_extendTensor A V V' N) _).symm,
        (isBaseChange_eigenMapAlgebra_of_flat (extendTensor_equivariant V V' ρ)
          (isBaseChange_extendTensor A V V' N) _).equiv, fun x => by simp⟩
  · intro V _ _ _ M M' _ _ _ _ τ τ' e he χ
    have he' : IsEquivariant τ τ' (e : M →ₗ[V] M') := he
    refine ⟨he'.map_eigenSub χ, fun K _ _ _ n c c' F F' hc hc' hF => ?_⟩
    have := flat_of_valuationRing V K
    exact he'.exists_triangular c c' hc hc' hF

open EigenSplit in

theorem eigenBundle {E : Type*} [Field E] [NumberField E]
    {L : Type*} [Field L] [CharZero L] [Fintype (E →+* L)] [DecidableEq (E →+* L)]
    (hL : ∀ x : E, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits)
    {A : Type u} [CommRing A] [IsDomain A] [Module.Flat ℤ A] [Algebra (𝓞 L) A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Projective A N]
    (ρ : 𝓞 E →+* Module.End A N) :
    ∃ r : (E →+* L) → ℕ,
      (∀ i, Module.rank A (eigenSub ρ (conjugateHom L A i)) = r i) ∧
      (Nontrivial (Localization.Away (NumberField.discr E : A)) ∧
        IsUnit (NumberField.discr E : Localization.Away (NumberField.discr E : A))) ∧
      (∀ (S : Type u) [CommRing S] [Algebra A S], IsUnit (NumberField.discr E : S) →
        DirectSum.IsInternal
          (fun i => eigenSub (baseChangeAction S ρ) ((algebraMap A S).comp (conjugateHom L A i))) ∧
        ∀ i, eigenSub (baseChangeAction S ρ) ((algebraMap A S).comp (conjugateHom L A i))
            = (eigenSub ρ (conjugateHom L A i)).baseChange S ∧
          Module.Finite S (eigenSub (baseChangeAction S ρ) ((algebraMap A S).comp (conjugateHom L A i))) ∧
          Module.Projective S
            (eigenSub (baseChangeAction S ρ) ((algebraMap A S).comp (conjugateHom L A i))) ∧
          ∀ p : PrimeSpectrum S, Module.rankAtStalk
            (eigenSub (baseChangeAction S ρ) ((algebraMap A S).comp (conjugateHom L A i))) p = r i) ∧
      (∀ (S : Type u) [CommRing S] [Algebra A S] [Module.Free S (S ⊗[A] N)],
        (∀ a, (baseChangeAction S ρ a).charpoly
          = ∏ i, (X - C (algebraMap A S (conjugateHom L A i a))) ^ r i) ∧
        (¬ IsNilpotent (NumberField.discr E : S) → ∀ r' : (E →+* L) → ℕ,
          (∀ a, (baseChangeAction S ρ a).charpoly
            = ∏ i, (X - C (algebraMap A S (conjugateHom L A i a))) ^ r' i) → r' = r)) ∧
      (∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [CharZero V] [Algebra A V]
        (i : (E →+* L)) (P : Submodule V (V ⊗[A] N)),
        P = eigenSub (baseChangeAction V ρ) ((algebraMap A V).comp (conjugateHom L A i)) →
        IsSaturatedSubmodule P ∧ P = saturation ((eigenSub ρ (conjugateHom L A i)).baseChange V) ∧
        Module.Finite V P ∧ Module.Free V P ∧ Module.finrank V P = r i ∧
        (∃ Q, IsCompl P Q) ∧
        (∀ (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K] [Algebra A K]
          [IsScalarTower A V K] (W : Submodule K (K ⊗[A] N)),
          W = eigenSub (baseChangeAction K ρ) ((algebraMap A K).comp (conjugateHom L A i)) →
          Function.Injective (extendTensor A V K N) ∧ IsBaseChange K (extendTensor A V K N) ∧
          P = (W.restrictScalars V).comap (extendTensor A V K N) ∧
          Submodule.span K (extendTensor A V K N '' P) = W ∧ Module.finrank K W = r i) ∧
        ∀ (V' : Type u) [CommRing V'] [IsDomain V'] [ValuationRing V'] [Algebra V V']
          [FaithfulSMul V V'] [Algebra A V'] [IsScalarTower A V V'] (P' : Submodule V' (V' ⊗[A] N)),
          P' = eigenSub (baseChangeAction V' ρ) ((algebraMap A V').comp (conjugateHom L A i)) →
          Submodule.span V' (extendTensor A V V' N '' P) = P' ∧
          ∃ e : V' ⊗[V] P ≃ₗ[V'] P', ∀ x : P,
            (e (1 ⊗ₜ x) : V' ⊗[A] N) = extendTensor A V V' N x) ∧
      ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
        (M M' : Type v) [AddCommGroup M] [Module V M] [AddCommGroup M'] [Module V M']
        (τ : 𝓞 E →+* Module.End V M) (τ' : 𝓞 E →+* Module.End V M') (e : M ≃ₗ[V] M'),
        (∀ a x, e (τ a x) = τ' a (e x)) → ∀ χ : 𝓞 E →+* V,
        (eigenSub τ χ).map (e : M →ₗ[V] M') = eigenSub τ' χ ∧
        ∀ (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K] (n : ℕ)
          (c : Module.Basis (Fin n) V (eigenSub τ χ)) (c' : Module.Basis (Fin n) V (eigenSub τ' χ))
          (F : Fin n → Submodule K (K ⊗[V] M)) (F' : Fin n → Submodule K (K ⊗[V] M')),
          (∀ k, Submodule.span K ((fun j => (1 : K) ⊗ₜ[V] (c j : M)) '' Set.Iic k) = F k) →
          (∀ k, Submodule.span K ((fun j => (1 : K) ⊗ₜ[V] (c' j : M')) '' Set.Iic k) = F' k) →
          (∀ k, (F k).map ((e : M →ₗ[V] M').baseChange K) = F' k) →
          ∃ g : GL (Fin n) V, (g : Matrix (Fin n) (Fin n) V).IsUpperTriangular ∧
            (∀ j, IsUnit (g j j)) ∧ (∀ k, e (c k) = ∑ j, g j k • (c' j : M')) ∧
            ∀ g' : Matrix (Fin n) (Fin n) K,
              (∀ k, (1 : K) ⊗ₜ[V] e (c k) = ∑ j, g' j k • (1 : K) ⊗ₜ[V] (c' j : M')) →
              g' = (g : Matrix (Fin n) (Fin n) V).map (algebraMap V K) :=
  have : CharZero A := flat_int_iff_charZero.1 ‹_›
  eigenBundle_of_injective
    (conjugateHom_injective Function.injective_id (card_embeddings_of_splits hL))
    (card_embeddings_of_splits hL) ρ

open EigenSplit in

example (E : Type) [Field E] [NumberField E] :
    ∃ r : (E →+* ℂ) → ℕ, ∀ i, Module.rank (𝓞 ℂ) (eigenSub (baseChangeAction (𝓞 ℂ)
      (Algebra.lmul ℤ (𝓞 E)).toRingHom) (conjugateHom ℂ (𝓞 ℂ) i)) = r i := by
  classical
  have : Module.Flat ℤ (𝓞 ℂ) := flat_int_iff_charZero.2 inferInstance
  obtain ⟨r, hr, -⟩ := eigenBundle.{0, 0} (L := ℂ) (A := 𝓞 ℂ) (fun _ => IsAlgClosed.splits _)
    (baseChangeAction (𝓞 ℂ) (Algebra.lmul ℤ (𝓞 E)).toRingHom)
  exact ⟨r, hr⟩

end GlobalTheory
