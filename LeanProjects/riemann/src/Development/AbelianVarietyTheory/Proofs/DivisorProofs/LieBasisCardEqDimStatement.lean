import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisCardEqDim
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_basis_card_eq_dim : ∀ (K : Type) [Field K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (n : ℕ) (v : Fin n → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR K ⟶ P.A)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v → P.g = n := by
  first | exact @GlobalTheory.LieDim.dim_eq_length | exact GlobalTheory.LieDim.dim_eq_length | (intros; apply GlobalTheory.LieDim.dim_eq_length <;> assumption)
