import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocFlat.CFac

def prodSBBil (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    SB X →ₗ[ℂ] SB Y →ₗ[ℂ] SB (X × Y) :=
  LinearMap.mk₂ ℂ prodSB
    (fun f f' g => by ext p; simp [add_mul])
    (fun c f g => by ext p; simp [mul_assoc])
    (fun f g g' => by ext p; simp [mul_add])
    (fun c f g => by ext p; simp; ring)

def tensorToProd (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    SB X ⊗[ℂ] SB Y →ₗ[ℂ] SB (X × Y) := TensorProduct.lift (prodSBBil X Y)

theorem tensorToProd_tmul {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : SB X) (g : SB Y) :
    tensorToProd X Y (f ⊗ₜ g) = prodSB f g := by
  simp [tensorToProd, prodSBBil]

theorem tensorToProd_injective (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    Function.Injective (tensorToProd X Y) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ (SB X)
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht' : t = c.sum fun i n => b i ⊗ₜ n := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : ∀ x y, ∑ i ∈ c.support, (b i).1 x * (c i).1 y = 0 := by
    intro x y
    have := congrArg (fun F : SB (X × Y) => F.1 (x, y)) ht
    simp only [ht', Finsupp.sum, map_sum, tensorToProd_tmul] at this
    simpa [Submodule.coe_sum, Finset.sum_apply] using this
  have hzero : c = 0 := by
    ext i y
    by_cases hi : i ∈ c.support
    · have hli := (linearIndependent_iff'.mp b.linearIndependent) c.support (fun i => (c i).1 y)
        (by
          ext x
          simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply]
          rw [← hm x y]
          exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)) i hi
      simpa using hli
    · simp [Finsupp.notMem_support_iff.mp hi]
  rw [ht', hzero]
  simp

end GlobalTheory.LocFlat.CFac

namespace GlobalTheory.LocFlat.CFac

theorem exists_linear_of_bilinear_prodSB : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (M : Type) [AddCommGroup M] [Module ℂ M] (B : SB X →ₗ[ℂ] SB Y →ₗ[ℂ] M), ∃ l : SB (X × Y) →ₗ[ℂ] M, ∀ f g, l (prodSB f g) = B f g := by
  intro X Y _ _ M _ _ B
  let m := tensorToProd X Y
  let e := LinearEquiv.ofInjective m (tensorToProd_injective X Y)
  let l₀ : LinearMap.range m →ₗ[ℂ] M := (TensorProduct.lift B).comp e.symm.toLinearMap
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  refine ⟨l, fun f g => ?_⟩
  have hmem : prodSB f g = ((e (f ⊗ₜ g) : LinearMap.range m) : SB (X × Y)) := by
    simp [e, LinearEquiv.ofInjective_apply, m, tensorToProd_tmul]
  have := LinearMap.congr_fun hl (e (f ⊗ₜ g))
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, l₀,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.lift.tmul] at this
  rw [hmem, this]

end GlobalTheory.LocFlat.CFac
