import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesTracePairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_coordinates_trace_pairing : ∀ (D : D7) (r : ℕ) (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∃ (n : ℕ) (c : (Fin n → AF D.host.F) ≃ₜ+ hermA D r) (u : Mx D r r → Fin n → AF D.host.F) (R : (Fin n → AF D.host.F) → Mx D r r), Continuous u ∧ Continuous R ∧ (∀ x : Mx D r r, x ∈ hermA D r → R (u x) = x) ∧ (∀ (v : Fin n → AF D.host.F) (x : Mx D r r), halfTr (Matrix.trace (HMul.hMul (c v).1 x : Mx D r r)) = v ⬝ᵥ u x) ∧ GlobalTheory.SWLit.IsTamagawa D.host.F (Fin n) (lam.map c.symm) := by
  first | exact @GlobalTheory.CompanionTheory.HermCoord.coords | exact GlobalTheory.CompanionTheory.HermCoord.coords | (intros; apply GlobalTheory.CompanionTheory.HermCoord.coords <;> assumption)
