import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteDvrResidueTranscendence
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_residue_transcendence : ∀ T : CDVR, ∃ (T' : CDVR) (φ : T.V →+* T'.V) (_ : IsLocalHom φ), Function.Injective φ ∧ ∃ t : ℕ → ResidueField T'.V, (letI := (ResidueField.map φ).toAlgebra; AlgebraicIndependent (ResidueField T.V) t) := by
  first | exact @GlobalTheory.GaussCountable.exists_gaussExtension | exact GlobalTheory.GaussCountable.exists_gaussExtension | (intros; apply GlobalTheory.GaussCountable.exists_gaussExtension <;> assumption)
