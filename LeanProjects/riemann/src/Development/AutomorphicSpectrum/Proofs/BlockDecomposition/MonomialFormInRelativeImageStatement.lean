import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormInRelativeImage
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_form_in_relative_image : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ) (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 → Tset g D.1 ⊆ S → ∃ ω ∈ relOm K (I0 n K S) a, omMap (incl le_top) a ω = monW K g D := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good <;> assumption)
