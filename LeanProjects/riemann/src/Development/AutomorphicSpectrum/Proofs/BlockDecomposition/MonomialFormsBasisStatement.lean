import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormsBasis
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_forms_basis : ∀ {K : Type} [Field K] {n d : ℕ} (a : ℕ), ∃ b : Module.Basis (Gam n d × {D : Finset (E n d) // D.card = a}) K (Om K (Lr K n d) a), ∀ p, b p = monW K p.1 p.2 := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.BasisW.monW_basis <;> assumption)
