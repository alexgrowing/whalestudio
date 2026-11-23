import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_res_lift : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W J J' : Ideal (MRing ι)) (D d : ℕ) (R : AnLogRes P J D) (R' : AnLogRes W J' d), J = ⊤ → P ≤ W → ∃ h : R'.X → R.X, HoloMap R'.A R.A h ∧ ∀ x, SameOrbit (R.lift (h x) (h x)) (R'.lift x x) := by
  intro K _ ι _ P W J J' D d R R' hJ hPW
  subst hJ
  exact GlobalTheory.CompanionTheory.Ar.PB.Proj.exists_holoMap_of_local_lifts R R'.A (V := R'.U) (μ := R'.lift)
    R'.isOpen_U R'.mem_U R'.holo
    (fun y u hu => ⟨(R'.mem y u hu).1, fun f hf => (R'.mem y u hu).2 f (hPW hf)⟩) R'.compat
