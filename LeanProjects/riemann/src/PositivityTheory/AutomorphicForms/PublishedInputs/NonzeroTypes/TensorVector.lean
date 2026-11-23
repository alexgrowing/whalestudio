import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ

namespace TensorVector

theorem tprod_ne_zero {ι : Type} [Fintype ι] {X : ι → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (x : ∀ a, X a) (hx : ∀ a, x a ≠ 0) :
    PiTensorProduct.tprod ℂ x ≠ 0 := by
  choose ℓ hℓ using fun a => Module.Projective.exists_dual_eq_one ℂ (hx a)
  intro h
  have h1 := congrArg (PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap ℓ)) h
  rw [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply] at h1
  simp [hℓ] at h1

end TensorVector

theorem step_tensorVec : TensorProductVectors := by
  intro k _ _ _ _ s d X _ _ σ μ h
  choose x hx0 hx using h
  refine ⟨PiTensorProduct.tprod ℂ x, TensorVector.tprod_ne_zero x hx0, fun m hm => ?_⟩
  rw [piTensor_tprod]
  have : (fun a => σ a (m a) (x a)) =
      fun a => ((μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ) • x a :=
    funext fun a => hx a (m a) (hm a)
  rw [this, MultilinearMap.map_smul_univ]

end UpperTheory.TNZ
