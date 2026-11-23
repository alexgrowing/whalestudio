import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPairingApproximation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_pairing_approximation : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (n N g : ℕ) {J : Type}
    (ta : Fin N → P.T) (x : Fin g → LieG P.Gt) (h : Fin N → Fin g → 𝓞_ℂ_[p]) (Tc : J → Fin N → 𝓞_ℂ_[p])
    (U : Fin g → 𝓞_ℂ_[p]), (∀ m b, h m b - (P.al₀ (ta m)).1 (x b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) → ∀ i : J,
    ‖(((∑ b, (∑ a, Tc i a * h a b) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) -
      P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))‖ ≤ (p : ℝ)⁻¹ ^ n := by
  first | exact @GlobalTheory.FlatModel.HTCong.pair_comb_congr | exact GlobalTheory.FlatModel.HTCong.pair_comb_congr | (intros; apply GlobalTheory.FlatModel.HTCong.pair_comb_congr <;> assumption)
