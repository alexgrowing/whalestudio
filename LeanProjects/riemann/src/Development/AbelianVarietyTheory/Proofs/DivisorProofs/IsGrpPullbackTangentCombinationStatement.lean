import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackTangentCombination
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
theorem _root_.GlobalTheory.T.isGrpPullback_tangent_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (S0 : Scheme.{0})
    (t : SAB H S0) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (x0 : Sp ℂ_[p] ⟶ S0)
    (ψ' : P.A.A.left ⟶ t.G.left), IsGrpPullback P.A.A t.G x0 ψ' →
    ∀ (m : ℕ) (xs : Fin m → LieG P.Gt) (us : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → 𝓞_ℂ_[p])
      (u : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), (∀ i, LieTie P ψ' (xs i) (us i)) →
      IsCombAtG t x0 us (fun i => algebraMap 𝓞_ℂ_[p] ℂ_[p] (a i)) u → LieTie P ψ' (lieComb P.Gt a xs) u := by
  first | exact @GlobalTheory.FlatModel.lieTie_lieComb | exact GlobalTheory.FlatModel.lieTie_lieComb | (intros; apply GlobalTheory.FlatModel.lieTie_lieComb <;> assumption)
