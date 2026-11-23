import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordsConjHermitianAdjoint
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittMixedCoords_conj_hermitianAdjoint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)), IsCovolOne (ratMx D ρ S.rank) μ 𝓕 → ∃ (μ' : Measure (Mx D S.rank ρ)) (𝓕' : Set (Mx D S.rank ρ)), IsCovolOne (ratMx D S.rank ρ) μ' 𝓕' ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.incAdj S y) = d.extX S (incA D D.host.xi0⁻¹ • y)) ∧ (∀ ξ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.incX S ξ) = d.extY S (giA S ⬝ adj ξ)) ∧ (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (d.inc0 S w) = d.ext0 S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T₀ w)) ∧ ∀ (f : WO S T → ℂ) y, d.mixS S ψ μ' 𝓕' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) (incA D D.host.xi0⁻¹ • y) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T₀ S) (d.mixT S ψ μ 𝓕 f y) := by
  first | exact @GlobalTheory.MixSwap.mixS_cj_dagger | exact GlobalTheory.MixSwap.mixS_cj_dagger | (intros; apply GlobalTheory.MixSwap.mixS_cj_dagger <;> assumption)
