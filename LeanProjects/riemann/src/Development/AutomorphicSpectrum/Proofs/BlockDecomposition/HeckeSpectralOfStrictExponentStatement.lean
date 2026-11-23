import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSpectralOfStrictExponent
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_spectral_of_strict_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → Zls.MaxExpStrict π → Zls.HeckeSpectral π := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict | exact GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict | (intros; apply GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict <;> assumption)
