import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingUnitScalar
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
theorem _root_.GlobalTheory.T.weil_pairing_unit_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (tι : Dw.La →+ P.T) (ζ : ℕ → ℂ_[p]ˣ),
    (∀ k, 0 < k → IsPrimitiveRoot (ζ k) k) → (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) →
    (∀ (k : ℕ) a b, weil P.A (p ^ k) ((tι a).lev k) ((tι b).lev k) = ζ (p ^ k) ^ Dw.EF a b) →
    ∃ u : ℤ_[p], IsUnit u ∧ ∀ a b, pairT P.A P.eps (tι a) (tι b) = u * (Dw.EF a b : ℤ_[p]) := by
  first | exact @GlobalTheory.TateUnitPair.main | exact GlobalTheory.TateUnitPair.main | (intros; apply GlobalTheory.TateUnitPair.main <;> assumption)
