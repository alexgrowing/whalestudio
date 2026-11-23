import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointLevelPower
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
theorem _root_.GlobalTheory.T.p_adic_point_level_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)], l'.A = p ^ n →
    ∀ (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
      (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∃ (ev : ℕ → Dw.La → (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)) (ζ : ℕ → ℂ_[p]ˣ),
      (∀ k, 0 < k → IsPrimitiveRoot (ζ k) k) ∧ (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) ∧
      (∀ k a b, ev k (a + b) = ev k a * ev k b) ∧ (∀ k (o : 𝓞 E) a, ev k (o • a) = ev k a ≫ P.oA.act o) ∧
      (∀ k, 0 < k → ∀ x, x ^ k = 1 ↔ ∃ a, ev k a = x) ∧
      (∀ k m, 0 < k → 0 < m → ∀ a, ev (k * m) a ^ m = ev k a) ∧
      (∀ k, 0 < k → ∀ a b, weil P.A k (ev k a) (ev k b) = ζ k ^ Dw.EF a b) ∧
      ∀ a, (ev (p ^ n) a).left ≫ ψ = yy ≫ (Y.oF.etaA a).left := by
  first | exact @GlobalTheory.FlatModel.tateIso_transport_ptOn | exact GlobalTheory.FlatModel.tateIso_transport_ptOn | (intros; apply GlobalTheory.FlatModel.tateIso_transport_ptOn <;> assumption)
