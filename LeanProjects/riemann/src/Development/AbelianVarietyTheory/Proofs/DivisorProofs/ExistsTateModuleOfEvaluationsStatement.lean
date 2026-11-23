import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleOfEvaluations
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tate_module_of_evaluations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p)
    (ev : ℕ → Dw.La → (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)), (∀ k a b, ev k (a + b) = ev k a * ev k b) →
    (∀ k (o : 𝓞 E) a, ev k (o • a) = ev k a ≫ P.oA.act o) →
    (∀ k m, 0 < k → 0 < m → ∀ a, ev (k * m) a ^ m = ev k a) → (∀ a, ev 1 a = 1) →
    ∃ tι : Dw.La →+ P.T, (∀ a k, (tι a).lev k = ev (p ^ k) a) ∧ ∀ (o : 𝓞 E) a, tι (o • a) = P.actT o (tι a) := by
  first | exact @GlobalTheory.FlatModel.tateLift_exists | exact GlobalTheory.FlatModel.tateLift_exists | (intros; apply GlobalTheory.FlatModel.tateLift_exists <;> assumption)
