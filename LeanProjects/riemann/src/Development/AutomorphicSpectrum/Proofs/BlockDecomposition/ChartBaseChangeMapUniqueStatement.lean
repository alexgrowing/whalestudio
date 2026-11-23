import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBaseChangeMapUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_base_change_map_unique : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) {S T : Finset (Fin d)} (θ₁ θ₂ : R0 K n d S →ₐ[K] C.R T), (∀ b, θ₁ (poly n K S b) = toR C T (phi C b)) → (∀ b, θ₂ (poly n K S b) = toR C T (phi C b)) → ∀ (θ' : R0 K n d T →ₐ[K] C.R T) (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b)), IsBaseChange (Aa C) (thetaLin C θ' hθ') → θ₁ = θ₂ := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique <;> assumption)
