import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

open Matrix in
open scoped TensorProduct ContDiff ComplexOrder in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in

theorem _root_.GlobalTheory.FockCompare.exists_heisenberg_operators : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), _root_.GlobalTheory.FockCompare.Sm ι f → ∀ (u : R) (w : G), _root_.GlobalTheory.FockCompare.hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → ∀ (M : Submodule ℂ (G → ℂ)), (∀ f ∈ M, _root_.GlobalTheory.FockCompare.Sm ι f) → (∀ u, ∀ f ∈ M, _root_.GlobalTheory.FockCompare.hD ι π om u f ∈ M) → ∃ Dop : R → Module.End ℂ M, (∀ u (f : M), ((Dop u f : M) : G → ℂ) = _root_.GlobalTheory.FockCompare.hD ι π om u f) ∧ (∀ u v, Dop (u + v) = Dop u + Dop v) ∧ ∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u := by
  intro G R _ _ _ _ ι π om _ hform M hSm hM
  have hdiff : ∀ f ∈ M, ∀ w : G, DifferentiableAt ℝ (fun x : R => f (w + ι x)) 0 :=
    fun f hf w => ((hSm f hf w).differentiable (by simp)).differentiableAt
  refine ⟨fun u =>
    { toFun := fun f => ⟨_root_.GlobalTheory.FockCompare.hD ι π om u f, hM u f f.2⟩
      map_add' := ?_
      map_smul' := ?_ }, fun u f => rfl, ?_, ?_⟩
  · intro f g
    ext w
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [hform _ (hSm _ (M.add_mem f.2 g.2)), hform _ (hSm _ f.2), hform _ (hSm _ g.2)]
    have hfun : (fun x : R => ((f : G → ℂ) + g) (w + ι x)) =
        (fun x : R => (f : G → ℂ) (w + ι x)) + fun x : R => (g : G → ℂ) (w + ι x) := rfl
    rw [hfun, fderiv_add (hdiff _ f.2 w) (hdiff _ g.2 w)]
    simp only [Pi.add_apply, ContinuousLinearMap.add_apply]
    ring
  · intro a f
    ext w
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [hform _ (hSm _ (M.smul_mem a f.2)), hform _ (hSm _ f.2)]
    have hfun : (fun x : R => (a • (f : G → ℂ)) (w + ι x)) =
        a • fun x : R => (f : G → ℂ) (w + ι x) := rfl
    rw [hfun, fderiv_const_smul (hdiff _ f.2 w)]
    simp only [Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.smul_apply]
    ring
  · intro u v
    ext f w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Submodule.coe_add,
      Pi.add_apply]
    rw [hform _ (hSm _ f.2), hform _ (hSm _ f.2), hform _ (hSm _ f.2)]
    simp only [map_add]
    push_cast
    ring
  · intro c u
    ext f w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, SetLike.val_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [hform _ (hSm _ f.2), hform _ (hSm _ f.2)]
    simp only [map_smul, smul_eq_mul, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.FockCompare
