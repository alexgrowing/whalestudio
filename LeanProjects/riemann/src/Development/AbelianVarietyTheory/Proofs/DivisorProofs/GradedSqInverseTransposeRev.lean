import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TendstoCutWt
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo

namespace GlobalTheory

theorem grSq_inv_transpose_rev : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), M.PosDef → ∀ i : Fin n,
    GlobalTheory.GradedNorm.grSq ((M⁻¹)ᵀ.submatrix Fin.rev Fin.rev) (Fin.rev i) = (GlobalTheory.GradedNorm.grSq M i)⁻¹ := by
  intro n M h i
  have := GlobalTheory.ShFam.MetsTest.grSq_dual_rev h (Fin.rev i)
  rwa [Fin.rev_rev] at this

end GlobalTheory
