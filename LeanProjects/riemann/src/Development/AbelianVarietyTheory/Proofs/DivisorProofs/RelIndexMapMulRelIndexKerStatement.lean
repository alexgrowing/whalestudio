import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexMapMulRelIndexKer
import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
open NumberField ReciprocityTheory.GeometryOfNumbersTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_map_mul_relIndex_ker : ∀ {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (A B : Submodule R M), A ≤ B → A.toAddSubgroup.relIndex B.toAddSubgroup = (A.map f).toAddSubgroup.relIndex (B.map f).toAddSubgroup * (A ⊓ LinearMap.ker f).toAddSubgroup.relIndex (B ⊓ LinearMap.ker f).toAddSubgroup := by
  first | exact @GlobalTheory.submodule_relIndex_split | exact GlobalTheory.submodule_relIndex_split | (intros; apply GlobalTheory.submodule_relIndex_split <;> assumption)
