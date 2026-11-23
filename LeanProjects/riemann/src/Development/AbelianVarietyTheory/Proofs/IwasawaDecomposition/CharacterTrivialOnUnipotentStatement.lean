import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnUnipotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trivial_on_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (γ : X.Γ), (((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → φ γ = 1 := by
  first | exact @GlobalTheory.UnipKill.char_eq_one_of_sq_eq_zero | exact GlobalTheory.UnipKill.char_eq_one_of_sq_eq_zero | (intros; apply GlobalTheory.UnipKill.char_eq_one_of_sq_eq_zero <;> assumption)
