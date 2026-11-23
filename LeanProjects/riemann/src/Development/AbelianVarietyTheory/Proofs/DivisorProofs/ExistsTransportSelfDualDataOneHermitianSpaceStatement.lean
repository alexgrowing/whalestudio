import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportSelfDualDataOneHermitianSpace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transport_selfDual_data_one_hermitianSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → ∃ Y'' : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y''.Ψ = Y.Ψ ∧ Y''.Gm = Y.Gm ∧ Y''.ξ0 = Y.ξ0 ∧ Y''.p0 = Y.p0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y'' ∧ GlobalTheory.EqCovol.IsSelfDualTr Y'' ∧ GlobalTheory.TrueCx.covol Y'' = GlobalTheory.TrueCx.covol Y' := by
  first | exact @GlobalTheory.EqCovol.exists_transport | exact GlobalTheory.EqCovol.exists_transport | (intros; apply GlobalTheory.EqCovol.exists_transport <;> assumption)
