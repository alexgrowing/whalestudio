import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelRestrictedTensorFixedHalf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_model_restricted_tensor_fixed_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ Λ' : AddSubgroup (WO S T)) (Φ f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → (∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) → IsSBHalf a Λ Φ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ' 1 (Tm (GlobalTheory.FinPl.PutIn.tens b Φ (halfInd b Λ))) (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensR b Φ) := by
  first | exact @GlobalTheory.FinPl.PutIn.Factor.isPlaceModel_tensR | exact GlobalTheory.FinPl.PutIn.Factor.isPlaceModel_tensR | (intros; apply GlobalTheory.FinPl.PutIn.Factor.isPlaceModel_tensR <;> assumption)
