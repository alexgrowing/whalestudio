import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatSectionEqHorizontalGenerator
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordAtConstMulIff
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_section_eq_horizontal_generator : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (τ : GlobalTheory.AllWt.Psi A.H) (hτ : τ.1 ∈ ((s.U κ.σ₀).X k).Ψ), ∀ f ∈ GlobalTheory.AllWt.secZ s.Xo κ.c (GlobalTheory.AllWt.exOf S.Dw (GlobalTheory.FlatLine.flatWt S.Dw τ) 0), IsFlat (Φ.C k) τ.1 ((Φ.C k).val f) → ∃ b : ℂˣ, ∀ x ∈ ((s.U κ.σ₀).X k).dom, Formalism.L2.PjFree.rdU (s.U κ.σ₀) f k x = b * GlobalTheory.FlatLine.horizGen ⟨τ.1, hτ⟩ x := by
  first | exact @GlobalTheory.ShFam.Horiz.rdU_eq_horizGen | exact GlobalTheory.ShFam.Horiz.rdU_eq_horizGen | (intros; apply GlobalTheory.ShFam.Horiz.rdU_eq_horizGen <;> assumption)
