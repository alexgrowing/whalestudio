import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNeg
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylAntisymmetrization_rename_swap_neg : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (τ : ι) (i j : Fin (m τ)), i ≠ j → rename (Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩) (antisymm Q) = -antisymm Q := by
  first | exact @GlobalTheory.AntisymmSwap.rename_swap_antisymm | exact GlobalTheory.AntisymmSwap.rename_swap_antisymm | (intros; apply GlobalTheory.AntisymmSwap.rename_swap_antisymm <;> assumption)
