import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicDivOfBeta
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem nfSq_of_fieldDat : GlobalTheory.NormSum.IntSt → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.TorEx → GlobalTheory.SqTop.BotSmall → NFSq := by
  intro hI hFD hTE hBS
  obtain ⟨CF0, h⟩ := GlobalTheory.SqTop.SqField.gBig_and hFD (GlobalTheory.SqTop.SqField.gBig_and hTE hBS)
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  refine ⟨x₀, fun D large₂ he hx hR T L μ₀ hμ G => ?_⟩
  obtain ⟨⟨_, _, _, _, hΛ⟩, hT, hQ, -, hB⟩ := h C0 le_rfl D large₂ he hx hR T L μ₀ hμ G
  exact GlobalTheory.SqTop.SqField.sqIn_of G μ₀ hI hΛ
    (fun i j s h1 h2 c => let ⟨x, a, b, _, d⟩ := hT i j s h1 h2 c; ⟨x, a, b, d⟩) hQ hB

end GlobalTheory.Mem.LiteralAutomorphy

end
