import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolume
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevelGroup_data_same_covolume : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, ∃ Y : ReciprocityTheory.ChartRestriction.G.FD.Data E r, Y.Ψ = (U.X k).Ψ ∧ Y.p0 = (U.X k).p0 ∧ Y.Gm = (U.X k).Gm ∧ Y.Λ = (U.X k).Λ ∧ Y.ξ0 = (U.X k).ξ0 ∧ GlobalTheory.EqCovol.IsLevGrp l Y ∧ GlobalTheory.EqCovol.IsSelfDualTr Y ∧ GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol Y := by
  first | exact @GlobalTheory.EqCovol.exists_levGrp_covol | exact GlobalTheory.EqCovol.exists_levGrp_covol | (intros; apply GlobalTheory.EqCovol.exists_levGrp_covol <;> assumption)
