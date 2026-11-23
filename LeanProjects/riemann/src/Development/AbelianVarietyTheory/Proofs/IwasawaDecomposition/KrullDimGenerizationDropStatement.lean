import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimGenerizationDrop
import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krull_dim_generization_drop : ∀ (X : Scheme.{0}) (q η : X), η ⤳ q → η ≠ q → ringKrullDim (X.presheaf.stalk q) ≤ 1 → ringKrullDim (X.presheaf.stalk η) ≤ 0 := by
  first | exact @GlobalTheory.ringKrullDim_stalk_nonpos_of_specializes_of_ne | exact GlobalTheory.ringKrullDim_stalk_nonpos_of_specializes_of_ne | (intros; apply GlobalTheory.ringKrullDim_stalk_nonpos_of_specializes_of_ne <;> assumption)
