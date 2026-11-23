import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_entire_and_normalizedJets_algebraic : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → Even a → Even b → (ambOf s B χ cD).ESmooth a b ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ), JetAlg (ambOf s B χ cD) a b S M := by
  first | exact @GlobalTheory.Mem.Col2.JetAlgebraic.esmooth_jetAlg | exact GlobalTheory.Mem.Col2.JetAlgebraic.esmooth_jetAlg | (intros; apply GlobalTheory.Mem.Col2.JetAlgebraic.esmooth_jetAlg <;> assumption)
