import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDataTateSpan
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
theorem _root_.GlobalTheory.T.lattice_data_tate_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (V : Type) [CommRing V]
    (β : V →+* 𝓞_ℂ_[p]) (σ : 𝓞 E →+* V) (J : Type) [DecidableEq J] (N : ℕ) (a : Fin N → Dw.La)
    (T S : J → Fin N → V) (tι : Dw.La →+ P.T), LatData Dw σ a T S → (∀ (o : 𝓞 E) b, tι (o • b) = P.actT o (tι b)) →
    Submodule.span ℤ_[p] (Set.range tι) = ⊤ →
    P.eigV (β.comp σ) ≤ Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) := by
  first | exact @GlobalTheory.FlatModel.EigSpan.eigV_le_span | exact GlobalTheory.FlatModel.EigSpan.eigV_le_span | (intros; apply GlobalTheory.FlatModel.EigSpan.eigV_le_span <;> assumption)
