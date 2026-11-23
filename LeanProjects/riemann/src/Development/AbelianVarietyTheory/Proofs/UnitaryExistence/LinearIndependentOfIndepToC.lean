import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BaseChangeTensorProduct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ReadingComparison

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
  ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {K L : Type} [Field K] [Field L] [Algebra K L] {σ : K →+* ℂ} {σ' : L →+* ℂ}
  {C W : Type} [AddCommGroup C] [Module K C] [AddCommGroup W] [Module ℂ W]

theorem bcMap_tmul (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) (t : L) (x : C) :
    BaseChangeTensorProduct.bcMap hσ f (t ⊗ₜ x) = σ' t • f x := rfl

theorem linearIndependent_of_indepToC {f : C →ₛₗ[σ] W} (hf : IndepToC f) {ι : Type} {b : ι → C}
    (hb : LinearIndependent K b) : LinearIndependent ℂ (fun i => f (b i)) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have e := s.equivFin
  have h1 := hf _ (fun i => b (e.symm i).1) (hb.comp (fun i => (e.symm i).1)
    (Subtype.val_injective.comp e.symm.injective))
  have h2 := h1.comp e e.injective
  convert h2 using 1
  funext i
  simp

theorem indepToC_bcMap_iff (hσ : ∀ a, σ' (algebraMap K L a) = σ a) (f : C →ₛₗ[σ] W) :
    IndepToC (BaseChangeTensorProduct.bcMap hσ f) ↔ IndepToC f := by
  constructor
  · intro h n b hb
    have h1 := h n (fun i => (1 : L) ⊗ₜ[K] b i) (Module.Flat.linearIndependent_one_tmul hb)
    simpa only [bcMap_tmul, map_one, one_smul] using h1
  · intro h n b hb
    letI : Algebra K ℂ := σ.toAlgebra
    letI : Algebra L ℂ := σ'.toAlgebra
    haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq fun a => (hσ a).symm
    letI : Module K W := Module.compHom W σ
    haveI : IsScalarTower K ℂ W := ⟨fun a z w => by
      show (σ a * z) • w = σ a • z • w
      rw [mul_smul]⟩
    let g : C →ₗ[K] W :=
      { toFun := f, map_add' := map_add f, map_smul' := fun a x => f.map_smulₛₗ a x }
    let F : ℂ ⊗[K] C →ₗ[ℂ] W := g.liftBaseChange ℂ
    let e := Module.Basis.ofVectorSpace K C
    have hF : Function.Injective F := by
      refine LinearMap.injective_of_linearIndependent (Algebra.TensorProduct.basis ℂ e).span_eq ?_
      have h0 := linearIndependent_of_indepToC h e.linearIndependent
      have e1 : (F ∘ Algebra.TensorProduct.basis ℂ e) = fun i => f (e i) := by
        funext i
        simp only [Function.comp, Algebra.TensorProduct.basis_apply, F, LinearMap.liftBaseChange_one_tmul]
        rfl
      rw [e1]; exact h0
    let φ := TensorProduct.AlgebraTensorModule.cancelBaseChange K L ℂ ℂ C
    have h1 : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[L] b i) := Module.Flat.linearIndependent_one_tmul hb
    have h2 := h1.map' (F ∘ₗ φ.toLinearMap) (LinearMap.ker_eq_bot.2 (hF.comp φ.injective))
    have key : ∀ x : L ⊗[K] C, F (φ ((1 : ℂ) ⊗ₜ[L] x)) = BaseChangeTensorProduct.bcMap hσ f x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul t x =>
        rw [bcMap_tmul]
        simp only [φ, F, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.liftBaseChange_tmul]
        show (σ' t * 1) • f x = _
        rw [mul_one]
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, map_add]
    have e2 : (fun i => BaseChangeTensorProduct.bcMap hσ f (b i)) = (F ∘ₗ φ.toLinearMap) ∘ fun i => (1 : ℂ) ⊗ₜ[L] b i :=
      funext fun i => (key (b i)).symm
    rw [e2]; exact h2

end General

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ)

end GlobalTheory.ReadingComparison
