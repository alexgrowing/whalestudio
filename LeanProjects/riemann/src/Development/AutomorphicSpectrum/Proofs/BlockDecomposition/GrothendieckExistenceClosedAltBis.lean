import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeClosedOfStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geClosed_of_statement_bot : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Scheme.{0}) [X.Over (Spec (.of R))] [IsSeparated (X ↘ Spec (.of R))] [LocallyOfFiniteType (X ↘ Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))], Statement I (⊥ : X.IdealSheafData)) → PositivityTheory.FormalThickening.GEClosed := by
  first | exact @GlobalTheory.CompanionTheory.GE.Close.geClosed_of_statement | exact GlobalTheory.CompanionTheory.GE.Close.geClosed_of_statement | (intros; apply GlobalTheory.CompanionTheory.GE.Close.geClosed_of_statement <;> assumption)
