import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticInvariantHermitianFunction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_invariant_hermitian_function : ∀ (g : ℕ) (F : symMat g → symMat g → Ext (1 + 1)), IsHermFun g F → (∀ γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g, IsInvFun F γ) → ∃ t l : ℝ, ∀ s ∈ siegel g, ∀ v : symMat g, F s v ∅ = t ∧ F s v Finset.univ = Complex.I * (l * sdens (tauU s) (tauU v) : ℝ) := by
  first | exact @GlobalTheory.InvHermSiegel.invHermFun_eq_const_and_smul_sdens | exact GlobalTheory.InvHermSiegel.invHermFun_eq_const_and_smul_sdens | (intros; apply GlobalTheory.InvHermSiegel.invHermFun_eq_const_and_smul_sdens <;> assumption)
