import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRoots
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_poly_chern_roots : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (S : MvPolynomial (Root m) ℝ), (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) → ∃ R : MvPolynomial (ι × ℕ) ℝ, chernRoots m R = S := by
  first | exact @GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric | exact GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric | (intros; apply GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric <;> assumption)
