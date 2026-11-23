import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionsEqUnivOffBadSupport
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsetOfClosedFibre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_eq_univ_off_bad_support : ∀ {X : Scheme.{0}} {P : X.Modules}, P.IsQuasicoherent → ∀ (S : Subobject P), (S : X.Modules).IsQuasicoherent → ∀ U : X.Opens, IsAffineOpen U → Disjoint (U : Set X) (GlobalTheory.CompanionTheory.GE.PSupp.badSet S) → secs S U = Set.univ := by
  first | exact @GlobalTheory.CompanionTheory.GE.PSupp.secs_eq_univ_of_disjoint_badSet | exact GlobalTheory.CompanionTheory.GE.PSupp.secs_eq_univ_of_disjoint_badSet | (intros; apply GlobalTheory.CompanionTheory.GE.PSupp.secs_eq_univ_of_disjoint_badSet <;> assumption)
