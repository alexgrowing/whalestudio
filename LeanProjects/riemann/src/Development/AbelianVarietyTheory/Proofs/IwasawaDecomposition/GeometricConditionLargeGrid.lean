import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridFieldHasLatticesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisorAllStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem rowGeo_at_gridA : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (CF : ℝ) (N : NExt hL) (S : SExt) (Γ : GeoP),
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c →
      Nonempty (GlobalTheory.HeightCounting.Up.NEl hL CF K B f T w Z Wt p0 t nch n xd c)) →
    RL.At (prmR (NEa hL N (GridA CF)) S Γ) R1.DivisorConditionAtBundlePoints → RL.At (prmR (NEa hL N (GridA CF)) S Γ) RL.Row_tie →
    RL.At (prmR (NEa hL N (GridA CF)) S Γ) fun Q L => RL.GeometricBoundCondition Q L CF := by
  intro hR hL CF N S Γ hN hD hT
  have hA := GlobalTheory.T.class_sum_divisor_all hR hL (NEa hL N (GridA CF)) S Γ
    (fun K B f T w Z Wt p0 t nch n xd c h => (hN K B f T w Z Wt p0 t nch n xd c h.1).map fun x => x.1) hD
  have hG : RL.At (prmR (NEa hL N (GridA CF)) S Γ) fun S L => Row S L (AtAll fun D O c (b : Bundle D O c) =>
      ∀ t : b.Comparison₂, (b.part t).pt.Ties → GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF) :=
    RL.At.of_row (RowE.row (GlobalTheory.T.grid_field_has_lattices hL CF N S Γ hN))
  obtain ⟨R, r, h⟩ := RowL.and (RowL.and hA hG) hT
  refine ⟨R, r, Row.imp h fun 𝒜 σ _ H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨t⟩ := H.2 Fm hc x hx i
  obtain ⟨a, b, c, d, e⟩ := H.1.1 Fm hc x hx i t
  exact ⟨t, a, b, c, d, e, H.1.2 Fm hc x hx i t c⟩

end GlobalTheory.Mem.LiteralAutomorphy
