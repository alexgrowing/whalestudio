import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCombinationLieGroupPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_combination_lie_group_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (π : P.G.left ⟶ t.G.left),
    IsGrpPullback P.G t.G yb π → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)) (xb : Fin g → LieG P.Gt),
    (∀ b, ITie P π (xb b) (e b)) → ∀ U : Fin g → 𝓞_ℂ_[p],
    ∃ u0 : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left, IsCombAtG t yb e U u0 ∧ ITie P π (lieComb P.Gt U xb) u0 := by
  first | exact @GlobalTheory.FlatModel.TieComb.main | exact GlobalTheory.FlatModel.TieComb.main | (intros; apply GlobalTheory.FlatModel.TieComb.main <;> assumption)
