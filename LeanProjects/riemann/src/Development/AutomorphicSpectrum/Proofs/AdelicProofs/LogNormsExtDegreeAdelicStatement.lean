import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelic
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logNorms_ext_degree_adelic : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (f : k →+* k') (N : LogNorms k), (N.ext f).deg = N.deg ∧ ((N.ext f).IsAdelic ↔ N.IsAdelic) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic | exact GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.logNorms_ext_deg_isAdelic <;> assumption)
