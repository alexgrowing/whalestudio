import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inner_product_smooth_vectors_tensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ ipD : SmT M →ₗ[ℂ] SmT M →ₗ⋆[ℂ] ℂ, (∀ v v' : M.Vec, ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') = ∏ τ, ⟪(v' τ : M.H τ), (v τ : M.H τ)⟫_ℂ) ∧ (∀ w w', ipD w w' = conj (ipD w' w)) ∧ ∀ w, w ≠ 0 → 0 < (ipD w w).re := by
  first | exact @GlobalTheory.ChainOnto.exists_ipD_smT | exact GlobalTheory.ChainOnto.exists_ipD_smT | (intros; apply GlobalTheory.ChainOnto.exists_ipD_smT <;> assumption)
