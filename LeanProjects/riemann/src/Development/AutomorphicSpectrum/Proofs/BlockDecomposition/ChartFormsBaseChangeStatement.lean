import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartFormsBaseChange
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_forms_base_change : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) {S : Finset (Fin d)} (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) → ∀ a : ℕ, IsBaseChange (Aa C) (psi C θ hθ a) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.isBaseChange_psi | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.isBaseChange_psi | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.isBaseChange_psi <;> assumption)
