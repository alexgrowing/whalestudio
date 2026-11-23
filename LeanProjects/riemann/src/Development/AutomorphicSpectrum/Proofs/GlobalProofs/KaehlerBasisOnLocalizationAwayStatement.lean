import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisOnLocalizationAway
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_basis_on_localization_away : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ} (x : Fin n → Γ(Y, U.1)), (letI := secAlgebra g U.1; ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) → IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away | exact GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away | (intros; apply GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away <;> assumption)
