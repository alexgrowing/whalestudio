import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroup
import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula PositivityTheory.FTA.FunctionalEquationHypotheses.B2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_skew_matrices_locally_compact_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
    (∀ β : Matrix (Fin n) (Fin n) (AE F E), β ∈ nA σ Y b ↔ βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0) →
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) ∧ IsTopologicalAddGroup (nA σ Y b) ∧
    LocallyCompactSpace (nA σ Y b) ∧ SecondCountableTopology (nA σ Y b) ∧ T2Space (nA σ Y b) ∧ BorelSpace (nA σ Y b) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRadTop.nA_top | exact GlobalTheory.CompanionTheory.SiegelRadTop.nA_top | (intros; apply GlobalTheory.CompanionTheory.SiegelRadTop.nA_top <;> assumption)
