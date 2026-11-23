import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_of_bilinear_schwartzBruhatProduct : ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (M : Type) [AddCommGroup M] [Module ℂ M] (B : SB X →ₗ[ℂ] SB Y →ₗ[ℂ] M), ∃ l : SB (X × Y) →ₗ[ℂ] M, ∀ f g, l (prodSB f g) = B f g := by
  first | exact @GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB | exact GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB | (intros; apply GlobalTheory.LocFlat.CFac.exists_linear_of_bilinear_prodSB <;> assumption)
