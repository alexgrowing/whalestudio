import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits
open scoped TensorProduct
open TensorProduct

noncomputable section

namespace GlobalTheory.HTW

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem map_mem_FilV (f : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈ FilV PD (LL := LL) (V := V') a := by
  rw [FilV, LinearMap.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map f LinearMap.id y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add y z hy hz => simp only [map_add, hy, hz]

private theorem algebraTensorModule_map_id_eq_rTensor (f : V →ₗ[LL] V') (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x = (f.restrictScalars Qp).rTensor BdR x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add y z hy hz => simp only [map_add, hy, hz]

private theorem comap_ker_sub_eq_ker_sub_of_injective_intertwining {M M' : Type} [AddCommGroup M] [Module LL M] [AddCommGroup M'] [Module LL M']
    (F : M →ₗ[LL] M') (hF : Function.Injective F) (A B : M →ₗ[LL] M) (A' B' : M' →ₗ[LL] M')
    (hA : ∀ x, A' (F x) = F (A x)) (hB : ∀ x, B' (F x) = F (B x)) :
    (LinearMap.ker (A' - B')).comap F = LinearMap.ker (A - B) := by
  ext x
  rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, hA, hB,
    ← map_sub]
  exact map_eq_zero_iff F hF

private theorem mem_filV_iff_of_isScalarTower {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    (a : ℤ) (y : W ⊗[Qp] BdR) :
    y ∈ FilV PD (LL := LL) (V := W) a ↔ (((PD.Fil a).restrictScalars Qp).mkQ.lTensor W) y = 0 := by
  have e : ∀ z, AlgebraTensorModule.map (LinearMap.id : W →ₗ[LL] W) ((PD.Fil a).restrictScalars Qp).subtype z =
      (((PD.Fil a).restrictScalars Qp).subtype.lTensor W) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [← LinearMap.mem_ker, lTensor_mkQ, FilV, LinearMap.mem_range, LinearMap.mem_range]
  simp only [e]

private theorem filV_comap_tensorMap_of_injective (f : V →ₗ[LL] V') (hf : Function.Injective f) (a : ℤ) :
    (FilV PD (LL := LL) (V := V') a).comap (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) =
      FilV PD (LL := LL) (V := V) a := by
  ext x
  rw [Submodule.mem_comap, mem_filV_iff_of_isScalarTower, mem_filV_iff_of_isScalarTower, algebraTensorModule_map_id_eq_rTensor]
  have hc : ((PD.Fil a).restrictScalars Qp).mkQ.lTensor V' ((f.restrictScalars Qp).rTensor BdR x) =
      (f.restrictScalars Qp).rTensor _ (((PD.Fil a).restrictScalars Qp).mkQ.lTensor V x) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [hc]

  exact map_eq_zero_iff _ (Module.Flat.rTensor_preserves_injective_linearMap (f.restrictScalars Qp) hf)

private theorem injective_algebraTensorModule_map_id_of_injective (f : V →ₗ[LL] V') (hf : Function.Injective f) :
    Function.Injective (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) := by
  intro x y hxy
  rw [algebraTensorModule_map_id_eq_rTensor, algebraTensorModule_map_id_eq_rTensor] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap (f.restrictScalars Qp) hf hxy

private theorem ddRE_comap_tensorMap_eq_of_injective_equivariant (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : Function.Injective f) (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) :
    (DdRE PD ρ' τ).comap (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) = DdRE PD ρ τ := by
  have hF := injective_algebraTensorModule_map_id_of_injective f hf (Qp := Qp) (BdR := BdR)
  rw [DdRE, DdRE, Submodule.comap_inf, DdR, DdR, Submodule.comap_iInf, Submodule.comap_iInf]
  congr 1
  · refine iInf_congr fun g => comap_ker_sub_eq_ker_sub_of_injective_intertwining _ hF _ _ _ _ ?_ (fun x => rfl)
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVdR, he]
    | add y z hy hz => simp only [map_add, hy, hz]
  · refine iInf_congr fun c => comap_ker_sub_eq_ker_sub_of_injective_intertwining _ hF _ _ _ _ ?_ ?_
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [mulVdR]
      | add y z hy hz => simp only [map_add, hy, hz]
    · intro x
      simp

theorem FildR_eq_comap (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : Function.Injective f) (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a = (FildR PD ρ' τ a).comap
      (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) := by
  rw [FildR, FildR, Submodule.comap_inf, ddRE_comap_tensorMap_eq_of_injective_equivariant PD ρ ρ' f hf he τ, filV_comap_tensorMap_of_injective PD f hf a]

end

theorem isJumpV_of_injective : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V'), Function.Injective f → (∀ g v, f (ρ g v) = ρ' g (f v)) → ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD ρ τ a → IsJumpV PD ρ' τ a := by
  intros
  rename_i ρ ρ' f hf he τ a hJ
  unfold IsJumpV at hJ ⊢
  intro h
  apply hJ
  rw [FildR_eq_comap _ _ _ _ hf he, FildR_eq_comap _ _ _ _ hf he, h]

end GlobalTheory.HTW
